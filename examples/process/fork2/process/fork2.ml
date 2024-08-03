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

type q_state = Q0 of int
[@@deriving show { with_path=false }, eq, ord, hash]

(*
  Q(x) = a?i -> (Q(x) ||| P(i))
      [] c?y -> Q(x + y)             -- retrieve the result
*)

let sync (ch : Channel.t) =
  match ch with
    C _pid -> true
  | _ -> false

(*
  naive use of P.composition has two problems:
  1. OMEGA will never be removed.
  2. two instances of the process P with the same pid
     conflicts on the channel c.
  the second problem can easily be solved by using hide.
*)

let q_transf pk state =
  match state with
    Q0 x ->
    [Receive (A, guard_true,
              (fun (A pid) ->
                let p = P.make_process (List.nth ps pid) P0 in
                P.composition event_to_channel sync [pk (Q0 x); p]) [@ocaml.warning "-8"])]
    @ List.map
        (fun pid ->
          Receive (C pid, guard_true,
                   (fun (C (_, y)) -> pk (Q0 (x + y))) [@ocaml.warning "-8"]))
        dom_pid

let q_class =
  P.make_process_class q_transf compare_q_state hash_q_state
    show_q_state (Q0 0)
