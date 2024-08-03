open Base.Hash.Builtin
open Process_model

module Event =
  struct
    type t = A of int | B of int * int | C of int * int
                 | Rd of int | Wr of int
    [@@deriving show { with_path=false }, eq, ord, hash]
  end

module Channel =
  struct
    type t = A | B of int | C of int | Rd | Wr
    [@@deriving show { with_path=false }, eq, ord, hash]
end

let event_to_channel (e : Event.t) : Channel.t =
  match e with
    A _ -> A
  | B (pid, _) -> B pid
  | C (pid, _) -> C pid
  | Rd _ -> Rd
  | Wr _ -> Wr

module P = Process.Make (Event) (Channel)
open P

(**************************************************************************)

let memo_transf pk x =
  [Event (Rd x, pk (-1));
   Receive (Wr, guard_true, (fun (Wr x) -> pk x) [@ocaml.warning "-8"])]

let memo_class =
  P.make_process_class memo_transf
    compare hash_int
    (fun x -> Printf.sprintf "%d" x)
    0

let memo = P.make_process memo_class (-1)

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
  Q(x) = a?i -> ((Q(x) [|c.i|] P(i)) \ c.i); rd?x -> Q(x)
      [] c?i?y -> wr!(x+y) -> SKIP
*)

type q_state = Q0 | Q1 of int | Q2 of int
[@@deriving show { with_path=false }, eq, ord, hash]

let sync (ch : Channel.t) =
  match ch with
    C _pid -> true
  | _ -> false

let q_transf pk state =
  match state with
    Q0 ->
     [Receive (Rd, guard_true,
               (fun (Rd x) -> pk (Q1 x)) [@ocaml.warning "-8"])]
  | Q1 x ->
     [Receive (A, guard_true,
               (fun (A pid) ->
                 let p = P.make_process (List.nth ps pid) P0 in
                 let pq = P.composition event_to_channel sync [pk (Q1 x); p] in
                 let hpq = P.hide event_to_channel sync pq in
                 P.sequential_composition hpq (pk Q0))
                 [@ocaml.warning "-8"])]
     @ List.map
         (fun pid ->
           Receive (C pid, guard_true,
                    (fun (C (_, y)) -> pk (Q2 (x+y))) [@ocaml.warning "-8"]))
         dom_pid
  | Q2 x ->
     [Event (Wr x, skip)]

let q_class =
  P.make_process_class q_transf compare_q_state hash_q_state
    show_q_state Q0

(**************************************************************************)

let sync_memo (ch : Channel.t) =
  List.mem ch [Rd; Wr]

let sys =
  let q1 = P.make_process q_class (Q1 0) in
  P.composition event_to_channel sync_memo [q1; memo]
