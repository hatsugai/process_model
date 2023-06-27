open Printf
open Base.Hash.Builtin
open Process_model

module E =
  struct
    type event = A | B
    [@@deriving show { with_path=false }, eq, ord, hash]

    type channel = ChA | ChB
    [@@deriving show { with_path=false }, eq, ord, hash]

    let event_to_channel e =
      match e with
        A -> ChA
      | B -> ChB
  end

module P = Process.Make(E)
open E
open P

(**************************************************************************)

(* properties *)

type accum = {
    mutable p_x : int;
    mutable q_y : int;
}

let accum = { p_x = -1; q_y = -1 }

let prop () =
  accum.p_x + accum.q_y >= 9


(**************************************************************************)

type p_state = P0 of int
[@@deriving show { with_path=false }, eq, ord, hash]

let p_transf pk state =
  match state with
    P0 x -> [Event (A, pk (P0 ((x + 1) mod 5)))]

let p_pwalk state =
  match state with
    P0 x ->
    printf "pwalk: P %d\n" x;
    accum.p_x <- x

let p_class =
  P.make_process_class p_transf compare_p_state hash_p_state
    show_p_state ~pwalk:p_pwalk
    (P0 0)

let p = make_process p_class (P0 0)

(**************************************************************************)

type q_state = Q0 of int
[@@deriving show { with_path=false }, eq, ord, hash]

let q_transf pk state =
  match state with
    Q0 y -> [Event (B, pk (Q0 ((y + 1) mod 7)))]

let q_pwalk state =
  match state with
    Q0 y ->
    printf "pwalk: Q %d\n" y;
    accum.q_y <- y

let q_class =
  P.make_process_class q_transf compare_q_state hash_q_state
    show_q_state ~pwalk:q_pwalk (Q0 0)

let q = make_process q_class (Q0 0)

(**************************************************************************)

(* concurrent composition *)

let pq = P.interleave [p; q]

(**************************************************************************)

(* unfold (clone from verification) *)

    type event = P.event
    type channel = P.channel
    type ievent = P.H.t
    type process = P.process

    module A =
      struct
        type t = Tau | Tick | Event of P.event | Hid of P.event | ITick
        [@@deriving show { with_path=false }, eq, ord]
      end

    module V =
      struct
        type t = Tick | Event of P.event
        [@@deriving show { with_path=false }, eq, ord, hash]
      end

    let htag_to_atag htag =
      match htag with
        P.H.Tau -> A.Tau
      | ITick -> ITick
      | Hid e -> Hid e

    (*** unfold *******************************************************)

    type lts = {
        vis_transv : (event * int) list array;
        tau_transv : (ievent * int) list array;
        tickv : bool array;
      }

    type 'state ltsx = {
        lts : lts;
        statev : 'state array;
        show : int -> string;
      }

    let ht_to_vec length iter state0 ht =
      let n = length ht in
      let statev = Array.make n state0 in
      let vis_transv = Array.make n [] in
      let tau_transv = Array.make n [] in
      let tickv = Array.make n false in
      iter
        (fun s (i, r) ->
          let (vs, ts, tick) = !r in
          vis_transv.(i) <- vs;
          tau_transv.(i) <- ts;
          tickv.(i) <- tick;
          statev.(i) <- s)
        ht;
      let lts = { vis_transv; tau_transv; tickv } in
      (lts, statev)

    module PHT =
      Hashtbl.Make(
          struct
            type t = process
            let equal = P.equal_process
            let hash = P.hash_process
          end)

    let unfold0 channel_to_event_list p =
      let nil = ([], [], false) in
      let ht = PHT.create 0 in
      let que = Queue.create () in
      let add s path =
        match PHT.find_opt ht s with
          None ->
           let id = PHT.length ht in
           let r = ref nil in
           PHT.replace ht s (id, r);
           Queue.add (s, r, path) que;
           id
        | Some (id, _r) -> id
      in
      let _ = add p [] in
      while not (Queue.is_empty que) do
        let (p, r, path) = Queue.take que in

        (* @_@ check prop *)
        pwalk p;
        (if prop () then
           printf "PROP: %s\n" (show_process p));

        let (vists, tauts) = P.transitions p in
        let vs =
          List.fold_left
            (fun acc trans ->
              match trans with
                P.Event (e, q) ->
                 let id = add q ((p, A.Event e)::path) in
                 (e, id)::acc
              | Receive (ch, guard, targetf) ->
                 List.fold_left
                   (fun acc e ->
                     if guard e then
                       let q = targetf e in
                       let id = add q ((p, A.Event e)::path) in
                       (e, id)::acc
                     else
                       acc)
                   acc (channel_to_event_list ch))
            [] vists
        in
        let ts =
          List.map
            (fun (htag, q) ->
              let atag = htag_to_atag htag in
              let id = add q ((p, atag)::path) in (htag, id))
            tauts
        in
        r := (vs, ts, p#tick)
      done;
      ht

    let unfold channel_to_event_list p =
      let ht = unfold0 channel_to_event_list p in
      let (lts, statev) =
        ht_to_vec PHT.length PHT.iter p ht
      in
      let show i =
        P.show_process statev.(i)
      in
      { lts; statev; show }


(**************************************************************************)

let channel_to_event_list _ch = []

let ltsx = unfold channel_to_event_list pq

(**************************************************************************)

module S = Simulation.Make(P)

let () =
  S.simulation channel_to_event_list pq
