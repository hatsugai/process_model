open Process_model
open Fork4
open E

let dom_msg = [0; 1; 2]
let dom_memo = [0; 1; 2]

let ch_to_es ch =
  match ch with
    ChA -> List.map (fun pid -> A pid) dom_pid
  | ChB pid -> List.map (fun x -> B (pid, x)) dom_msg
  | ChC pid -> List.map (fun x -> C (pid, x)) dom_msg
  | ChRd -> List.map (fun x -> Rd x) dom_memo
  | ChWr -> List.map (fun x -> Wr x) dom_memo

module S = Simulation.Make(P)

let () =
  S.simulation ch_to_es sys
