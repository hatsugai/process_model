open Process_model
open Fork1
open Event

let dom_msg = [0; 1; 2]

let ch_to_event_list (ch : Channel.t) : Event.t list =
  match ch with
    A -> List.map (fun pid -> A pid) dom_pid
  | B pid -> List.map (fun x -> B (pid, x)) dom_msg
  | C pid -> List.map (fun x -> C (pid, x)) dom_msg

module S = Simulation.Make (P)

let () =
  let q = P.make_process q_class Q0 in
  S.simulation ch_to_event_list q
