open Base.Hash.Builtin

(* step 1. define events and channels *)

module E =
  struct
    type event = A | B of int | C of int
    [@@deriving show { with_path=false }, eq, ord, hash]

    type channel = ChA | ChB | ChC
    [@@deriving show { with_path=false }, eq, ord, hash]

    let event_to_channel e =
      match e with
        A -> ChA
      | B _ -> ChB
      | C _ -> ChC
  end

(* step 2. make process model module *)

module P = Process_model.Make(E)

open E
open P

(* step 3. define process states *)

type p_state = P0 | P1 of int
[@@deriving show { with_path=false }, eq, ord, hash]

(* step 4. define transition function *)

let guard_true _e = true

let p_transf pk state =
  match state with
    P0 -> [Event (A, skip);
           Receive (ChB, guard_true,
                    (fun (B x) -> pk (P1 x)) [@ocaml.warning "-8"])]
  | P1 x -> [Event (C x, pk P0)]

(* step 5. define process class *)

let p_class =
  make_process_class p_transf compare_p_state hash_p_state
    show_p_state P0

(* step 6. make a process instance *)

let p = make_process p_class P0

(* step 7. make simuation module *)

module S = Simulation.Make(P)

(* step 8. define a function from channel to event list *)

let dom = [0; 1; 2; 3]

let channel_to_event_list ch =
  match ch with
    ChA -> [A]
  | ChB -> List.map (fun x -> B x) dom
  | ChC -> List.map (fun x -> C x) dom

(* step 9. do simulation *)

let () =
  S.simulation channel_to_event_list p
