open Base.Hash.Builtin
open Process_model

(* step 1. define events and channels *)

module Event =
  struct
    type t = A | B of int | C of int
    [@@deriving show { with_path=false }, eq, ord, hash]
  end

module Channel =
  struct
    type t = A | B | C
    [@@deriving show { with_path=false }, eq, ord, hash]
  end

let event_to_channel (e : Event.t) : Channel.t =
  match e with
    A -> A
  | B _ -> B
  | C _ -> C

(* step 2. make process model module *)

module P = Process.Make (Event) (Channel)
open P

(* step 3. define process states *)

type p_state = P0 | P1 of int
[@@deriving show { with_path=false }, eq, ord, hash]

(* step 4. define transition function *)

let p_transf pk state =
  match state with
    P0 -> [Event (A, skip);
           Receive (B, guard_true,
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

let channel_to_event_list (ch : Channel.t) =
  match ch with
    A -> [Event.A]
  | B -> List.map (fun x -> Event.B x) dom
  | C -> List.map (fun x -> Event.C x) dom

(* step 9. do simulation *)

let () =
  S.simulation channel_to_event_list p
