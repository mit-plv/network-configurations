#use "topfind"
#thread
#require "openflow"
#require "openflow.async"

#use "./src/example_entries.ml"

let logical_or = Int32.logor
let int32_to_int = Int32.to_int

open Async.Std
open Core.Std

open OpenFlow0x01
open OpenFlow0x01_Core
open OpenFlow0x01.Message

let rec word_to_int32 w = match w with
  | WO -> 0l
  | WS (b, _, w') ->
    if b
      then Int32.succ (Int32.shift_left (word_to_int32 w') 1)
      else Int32.shift_left (word_to_int32 w') 1

let ip_to_mask ip =
  let int32_rep = logical_or
    (logical_or
      (Int32.shift_left (word_to_int32 (fst (fst (fst ip)))) 24)
      (Int32.shift_left (word_to_int32 (snd (fst (fst ip)))) 16)
    )
    (logical_or
      (Int32.shift_left (word_to_int32 (snd (fst ip))) 8)
      (word_to_int32 (snd ip))
    )
  in
    { m_value = int32_rep; m_mask = None }

let generate_flow_mod_message entry = FlowModMsg {
  command = AddFlow;
  priority = 1;
  cookie = 0L;
  idle_timeout = Permanent;
  hard_timeout = Permanent;
  notify_when_removed = false;
  apply_to_packet = None;
  out_port = None;
  check_overlap = false;
  pattern = { match_all with
    dlTyp = Some 0x800;
    nwSrc = (
      match entry.header_fields.ipSrcMatcher with
      | Some ip -> Some (ip_to_mask ip)
      | None -> None
    );
    nwDst = (
      match entry.header_fields.ipDestMatcher with
      | Some ip -> Some (ip_to_mask ip)
      | None -> None
    )
  };
  actions = match entry.action with
    | ForwardToPort p -> [Output (PhysicalPort (int32_to_int (word_to_int32 p)))]
    | Drop -> []
}

let generate_flow_mod_messages entry_list = List.map entry_list (fun entry ->
  marshal 1l (generate_flow_mod_message entry)
)


let example_node_A_entries = generate_flow_mod_messages (example_openflow_entries A)

(* TODO: This mapping should probably be generated from Coq code and/or provided by the user  *)
let switch_id_to_node id = match id with
  | 1L -> A
  | 2L -> B
  | 3L -> C
  | 4L -> D
  | 5L -> E
  | 6L -> F
  | _ -> failwith "Message from unknown switch"

let switch (ctl : Async_OpenFlow.OpenFlow0x01.Controller.t) _ evt =
  match evt with
    | `Connect (sw_id, _) ->
      Deferred.all (
        List.map (example_openflow_entries (switch_id_to_node sw_id)) (fun entry ->
          Async_OpenFlow.OpenFlow0x01.Controller.send ctl sw_id (1l, generate_flow_mod_message entry)
        )
      )
    | `Disconnect (_, _) ->
      return []
    | `Message (_, _) ->
      return []


let main () =
  Async_OpenFlow.OpenFlow0x01.Controller.create 6633 () >>=
    fun t ->
      Pipe.fold (Async_OpenFlow.OpenFlow0x01.Controller.listen t) ~init:[] ~f:(switch t)

let _ = main ()
let _ = never_returns (Scheduler.go ())
