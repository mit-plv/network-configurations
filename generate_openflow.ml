#use "topfind"
#thread
#require "openflow"
#require "openflow.async"

#use "output/example_entries.ml"

let logical_or = Int32.logor;;
let int32_to_int = Int32.to_int;;

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
      else Int32.shift_left (word_to_int32 w') 1;;

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
    { m_value = int32_rep; m_mask = None };;


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
};;

let generate_flow_mod_messages entry_list = List.map entry_list (fun entry ->
  marshal 1l (generate_flow_mod_message entry)
);;


let example_node_A_entries = generate_flow_mod_messages (example_openflow_entries A);;
