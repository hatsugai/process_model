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

let state_var = ref 0

let prop p =
  pwalk p;
  !state_var = -108


(**************************************************************************)

type p_state = P of int
[@@deriving show { with_path=false }, eq, ord, hash]

let p_transf pk state =
  match state with
    P x ->
    if x < 60 then
      [Event (A, pk (P (x * 4))); Event (B, pk (P (x * 4 + 2)))]
    else
      [Event (A, pk (P (x / 3)))]

let p_pwalk state =
  match state with
    P x -> state_var := x

let p_class =
  P.make_process_class p_transf compare_p_state hash_p_state
    show_p_state ~pwalk:p_pwalk
    (P 0)

let p = make_process p_class (P 1)

let event_set ch = (ch = ChB)

let hp = P.hide event_set p


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

    type vis_trans = (event * int) list
    type tau_trans = (ievent * int) list
    type ht = (int * (vis_trans * tau_trans * bool) ref) PHT.t
    exception Unfold_Prop of ht * process * (process * A.t) list

    let unfold0 prop channel_to_event_list p =
      let nil = ([], [], false) in
      let level = ref 0 in
      let dup = ref 0 in
      let ht = PHT.create 0 in
      let que0 = ref (Queue.create ()) in
      let que1 = ref (Queue.create ()) in
      let swap () =
        let tmp = !que0 in
        que0 := !que1;
        que1 := tmp;
        Queue.clear !que1
      in
      let add s path =
        match PHT.find_opt ht s with
          None ->
           let id = PHT.length ht in
           let r = ref nil in
           PHT.replace ht s (id, r);
           Queue.add (s, r, path) !que1;
           id
        | Some (id, _r) ->
           dup := !dup + 1;
           id
      in
      let _ = add p [] in
      while not (Queue.is_empty !que1) do
        printf "%d %d %d\n" !level (Queue.length !que1) !dup;
        flush stdout;
        level := !level + 1;
        dup := 0;
        swap ();
        while not (Queue.is_empty !que0) do
          let (p, r, path) = Queue.take !que0 in
          (* @_@ prop *)
          (if prop p then
             raise (Unfold_Prop (ht, p, path)));
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
      done;
      ht

    let unfold ?(prop = (fun _ -> false)) channel_to_event_list p =
      let ht = unfold0 prop channel_to_event_list p in
      let (lts, statev) =
        ht_to_vec PHT.length PHT.iter p ht
      in
      let show i =
        P.show_process statev.(i)
      in
      { lts; statev; show }


(**************************************************************************)

let viz name show_state lts path =
  let n = Array.length lts.vis_transv in
  let emit_states ch =
    for id=0 to n-1 do
      fprintf ch "%d [label=\"%d\\n%s\"];\n" id id (show_state id)
    done
  in
  let emit_transitions ch =
    let emit_vis_trans sid (event, tid) =
      fprintf ch "%d -> %d [label=\"%s\"];\n" sid tid (show_event event)
    in
    let emit_tau_trans sid (ievent, tid) =
      fprintf ch "%d -> %d [label=\"%s\"];\n" sid tid (P.H.show ievent)
    in
    for id=0 to n-1 do
      let trans = lts.vis_transv.(id) in
      List.iter (emit_vis_trans id) trans
    done;
    for id=0 to n-1 do
      let trans = lts.tau_transv.(id) in
      List.iter (emit_tau_trans id) trans
    done
  in
  let ch = open_out (name ^ ".dot") in
  fprintf ch "digraph {\n";
  emit_states ch;
  emit_transitions ch;
  fprintf ch "}\n";
  close_out ch;
  let command = sprintf "dot -Tpdf -o %s.pdf %s.dot" name name in
  let _ = Unix.system command in
  ()

(**************************************************************************)

let channel_to_event_list _ch = []

let (lts, show_state, path) =
  try
    let ht = unfold0 prop channel_to_event_list hp in
    let (lts, statev) =
      ht_to_vec PHT.length PHT.iter p ht
    in
    let show i =
      P.show_process statev.(i)
    in
    (lts, show, [])
  with
    Unfold_Prop (ht, p, path) ->
    let (lts, statev) =
      ht_to_vec PHT.length PHT.iter p ht
    in
    let show i =
      P.show_process statev.(i)
    in
    (lts, show, path)

let () = printf "num of states: %d\n" (Array.length lts.tickv)
let () = viz "x" show_state lts path
