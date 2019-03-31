open Generated_controller
open Async.Std

let logical_or = Int32.logor
let int32_to_int = Int32.to_int
let int64_to_int = Int64.to_int
let int_to_int64 = Int64.of_int
let nth = List.nth

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

let ip_to_int32 ip = logical_or
  (logical_or
    (Int32.shift_left (word_to_int32 (fst (fst (fst ip)))) 24)
    (Int32.shift_left (word_to_int32 (snd (fst (fst ip)))) 16)
  )
  (logical_or
    (Int32.shift_left (word_to_int32 (snd (fst ip))) 8)
    (word_to_int32 (snd ip))
  )

let ip_to_mask ip = { m_value = ip_to_int32 ip; m_mask = None }

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
    | ForwardToSwitch p -> [Output (PhysicalPort (int32_to_int (word_to_int32 p)))]
    | ForwardToDest p -> [Output (PhysicalPort (int32_to_int (word_to_int32 p))); Output(Controller 1024)]
    | Drop -> []
}

let delete_all_flows_message = FlowModMsg {
  command = DeleteFlow;
  priority = 99;
  cookie = 0L;
  idle_timeout = Permanent;
  hard_timeout = Permanent;
  notify_when_removed = false;
  apply_to_packet = None;
  out_port = None;
  check_overlap = false;
  pattern = match_all;
  actions = []
}

let find_host_with_ip ip32 = List.find (filter_hosts all_nodes) (fun host -> ip_to_int32 (host_ip host) = ip32)

(* Note: This requires the user to arrange switch IDs in the same order as their Coq inductive type
 * i.e. the first switch has ID 1, second has ID 2, etc. *)
let switch_id_to_switch sw_id = nth (filter_switches all_nodes) (int64_to_int sw_id - 1)

let switch (ctl : Async_OpenFlow.OpenFlow0x01.Controller.t) (state) evt =
  match evt with
    | `Connect (sw_id, _) ->
      Deferred.all (
        List.map (generated_dynamic_controller.controller_state_decider state (switch_id_to_switch sw_id)) (fun entry ->
          Async_OpenFlow.OpenFlow0x01.Controller.send ctl sw_id (1l, generate_flow_mod_message entry)
        )
      ) >>= (fun _ -> return state)
    | `Disconnect (_, _) ->
      return state
    | `Message (sw_id, (_xid, msg)) ->
      match msg with
      | PacketInMsg pktIn ->
        (if pktIn.total_len <> 342 then
          Printf.printf
            "switch %Lu: %s\n%!"
            sw_id
            (packetIn_to_string pktIn)
        );
        if pktIn.reason = ExplicitSend
        then
          let packet = parse_payload pktIn.input_payload
          in let maybe_src_host = find_host_with_ip (Packet.nwSrc packet)
          in let maybe_dest_host = find_host_with_ip (Packet.nwDst packet)
          in match maybe_src_host, maybe_dest_host with
          | Some src_host, Some dest_host ->
            let processed_flow = { src = src_host; dest = dest_host }
            in let new_state = generated_dynamic_controller.controller_system.step state processed_flow
            in Deferred.all (
              List.mapi (filter_switches all_nodes) (fun index switch -> (
                let dest_switch_id = int_to_int64 (index + 1)
                in Async_OpenFlow.OpenFlow0x01.Controller.send ctl dest_switch_id (1l, delete_all_flows_message)
                  >>= fun _ -> Deferred.all (
                    List.map (generated_dynamic_controller.controller_state_decider new_state switch) (fun entry ->
                      Async_OpenFlow.OpenFlow0x01.Controller.send ctl dest_switch_id (1l, generate_flow_mod_message entry)
                    )
                  )
                )
              )
            ) >>= (fun _ -> print_endline "sent new flows"; return new_state)
          | _, _ -> return state
        else return state
      | ErrorMsg err ->
        print_endline "error message";
        return state
      | PortStatusMsg ps ->
        return state
      | _ ->
        print_endline "other";
        return state

let main () =
  Async_OpenFlow.OpenFlow0x01.Controller.create 6633 () >>=
    fun t ->
      Pipe.fold (Async_OpenFlow.OpenFlow0x01.Controller.listen t) ~init:(generated_dynamic_controller.controller_system.initial) ~f:(switch t)

let _ = main ()
let _ = never_returns (Scheduler.go ())
