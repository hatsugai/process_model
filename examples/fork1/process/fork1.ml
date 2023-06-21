open Base.Hash.Builtin
open Process_model

module E =
  struct
    type event = A of int | B of int * int | C of int * int
    [@@deriving show { with_path=false }, eq, ord, hash]

    (*
      the 1st parameter of the channels B and C are structural parameters.
      they are regarded as constants.
     *)
    type channel = ChA | ChB of int | ChC of int
    [@@deriving show { with_path=false }, eq, ord, hash]

    let event_to_channel e =
      match e with
        A _ -> ChA
      | B (pid, _) -> ChB pid
      | C (pid, _) -> ChC pid
  end

module P = Process.Make(E)
open E
open P

(**************************************************************************)

(*
  P(i) = b.i?x -> c.i!x -> SKIP
*)

type p_state = P0 | P1 of int
[@@deriving show { with_path=false }, eq, ord, hash]

let p_transf pid pk state =
  match state with
    P0 -> [Receive (ChB pid, (fun _ -> true), (fun (B (_, x)) -> pk (P1 x)))]
            [@ocaml.warning "-8"]
  | P1 x -> [Event (C (pid, x), skip)]

let mk_p_class pid =
  P.make_process_class (p_transf pid) compare_p_state hash_p_state
    (fun s -> Printf.sprintf "%d:%s" pid (show_p_state s))
    P0

let dom_pid = [0; 1; 2]

let ps = List.map mk_p_class dom_pid

(**************************************************************************)

type q_state = Q0
[@@deriving show { with_path=false }, eq, ord, hash]

(*
  Q = a?i -> (Q ||| P(i))

  P.interleave automatically removes OMEGAs.
  (N.B. it is NOT equal to P [|{}|] Q.)
*)

let q_transf pk state =
  match state with
    Q0 ->
    [Receive (ChA, (fun _ -> true),
              (fun (A pid) ->
                let p = make_process (List.nth ps pid) P0 in
                P.interleave [pk Q0; p]) [@ocaml.warning "-8"])]

let q_class =
  P.make_process_class q_transf compare_q_state hash_q_state
    show_q_state Q0
