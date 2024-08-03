open Process_model
open Fork2

let dom_msg = [0; 1; 2]

let ch_to_es (ch : Channel.t) : Event.t list =
  match ch with
    A -> List.map (fun pid -> Event.A pid) dom_pid
  | B pid -> List.map (fun x -> Event.B (pid, x)) dom_msg
  | C pid -> List.map (fun x -> Event.C (pid, x)) dom_msg

module S = Simulation.Make (P)

let () =
  let q = P.make_process q_class (Q0 0) in
  S.simulation ch_to_es q
