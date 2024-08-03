open Process_model
open Fork4

let dom_msg = [0; 1; 2]
let dom_memo = [0; 1; 2]

let ch_to_es (ch : Channel.t) =
  let module E = Event in
  match ch with
    A -> List.map (fun pid -> E.A pid) dom_pid
  | B pid -> List.map (fun x -> E.B (pid, x)) dom_msg
  | C pid -> List.map (fun x -> E.C (pid, x)) dom_msg
  | Rd -> List.map (fun x -> E.Rd x) dom_memo
  | Wr -> List.map (fun x -> E.Wr x) dom_memo

module S = Simulation.Make (P)

let () =
  S.simulation ch_to_es sys
