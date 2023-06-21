open Process_model
open Fork2
open E

let dom_msg = [0; 1; 2]

let ch_to_es ch =
  match ch with
    ChA -> List.map (fun pid -> A pid) dom_pid
  | ChB pid -> List.map (fun x -> B (pid, x)) dom_msg
  | ChC pid -> List.map (fun x -> C (pid, x)) dom_msg

module S = Simulation.Make(P)

let () =
  let q = P.make_process q_class (Q0 0) in
  S.simulation ch_to_es q
