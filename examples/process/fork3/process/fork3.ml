open Base.Hash.Builtin
open Process_model

module Event =
  struct
    type t = A of int | B of int * int | C of int * int
    [@@deriving show { with_path=false }, eq, ord, hash]
  end


module Channel =
  struct
    type t = A | B of int | C of int
    [@@deriving show { with_path=false }, eq, ord, hash]
  end

let event_to_channel (e : Event.t) : Channel.t =
  match e with
    A _ -> A
  | B (pid, _) -> B pid
  | C (pid, _) -> C pid

module P = Process.Make (Event) (Channel)
open P

(**************************************************************************)

type p_state = P0 | P1 of int
[@@deriving show { with_path=false }, eq, ord, hash]

(*
  P(i) = b.i?x -> c.i!x -> SKIP
*)

let p_transf pid pk state =
  match state with
    P0 ->
     [Receive (B pid, guard_true,
               (fun (B (_, x)) -> pk (P1 x)) [@ocaml.warning "-8"])]
  | P1 x ->
     [Event (C (pid, x), skip)]

let mk_p_class pid =
  P.make_process_class (p_transf pid) compare_p_state hash_p_state
    (fun s -> Printf.sprintf "%d:%s" pid (show_p_state s))
    P0

let dom_pid = [0; 1; 2]

let ps = List.map mk_p_class dom_pid

(**************************************************************************)

(*
  Q = a?i -> ((Q [|c.i|] P(i)) \ c.i); Q
   [] c?i?x -> SKIP
*)

type q_state = Q0
[@@deriving show { with_path=false }, eq, ord, hash]

let sync (ch : Channel.t) =
  match ch with
    C _pid -> true
  | _ -> false

(*
  the combination of hide and seq make it possible to fold the process tree
  when the inner process terminates.
  however, child processes cannot pass values to the parent.
*)

let q_transf pk state =
  match state with
    Q0 ->
    [Receive (A, guard_true,
              (fun (A pid) ->
                let p = P.make_process (List.nth ps pid) P0 in
                let pq = P.composition event_to_channel sync [pk Q0; p] in
                let hpq = P.hide event_to_channel sync pq in
                P.sequential_composition hpq (pk Q0))
                [@ocaml.warning "-8"])]
    @ List.map
        (fun pid ->
          Receive (C pid, guard_true, (fun _ -> skip)))
        dom_pid

let q_class =
  P.make_process_class q_transf compare_q_state hash_q_state
    show_q_state Q0
