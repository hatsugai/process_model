open Type
open Process

module type Unfold =
  sig
    type event
    type channel
    type process

    module PHT : Hashtbl.S with type key = process

    type lts = {
      vis_transv : (event * int) list array;
      tau_transv : (event TransitionLabel.ievent * int) list array;
      tickv : bool array;
    }

    type visible_trans_list = (event * int) list
    type internal_trans_list = (event TransitionLabel.ievent * int) list
    type pht_ent = int * (visible_trans_list * internal_trans_list * bool) ref

    val unfold0 : (channel -> event list) -> process -> pht_ent PHT.t
    val ht_to_lts : pht_ent PHT.t -> process -> lts * process array
    val unfold : (channel -> event list) -> process -> lts * process array

  end

module Make (P : ProcessModel) : Unfold
       with type event = P.event
       with type channel = P.channel
       with type process = P.process
  =
  struct
    type event = P.event
    type channel = P.channel
    type process = P.process

    type visible_trans_list = (event * int) list
    type internal_trans_list = (event TransitionLabel.ievent * int) list
    type pht_ent = int * (visible_trans_list * internal_trans_list * bool) ref

    type lts = {
        vis_transv : (event * int) list array;
        tau_transv : (event TransitionLabel.ievent * int) list array;
        tickv : bool array;
      }

    module PHT =
      Hashtbl.Make(
          struct
            type t = process
            let equal = P.equal_process
            let hash = P.hash_process
          end)

    let ht_to_lts ht state0 =
      let n = PHT.length ht in
      let statev = Array.make n state0 in
      let vis_transv = Array.make n [] in
      let tau_transv = Array.make n [] in
      let tickv = Array.make n false in
      PHT.iter
        (fun s (i, r) ->
          let (vs, ts, tick) = !r in
          vis_transv.(i) <- vs;
          tau_transv.(i) <- ts;
          tickv.(i) <- tick;
          statev.(i) <- s)
        ht;
      let lts = { vis_transv; tau_transv; tickv } in
      (lts, statev)

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
        let (vists, tauts) = P.transitions p in
        let vs =
          List.fold_left
            (fun acc trans ->
              match trans with
                P.Event (e, q) ->
                 let id = add q ((p, TransitionLabel.Vis e)::path) in
                 (e, id)::acc
              | Receive (ch, guard, targetf) ->
                 List.fold_left
                   (fun acc e ->
                     if guard e then
                       let q = targetf e in
                       let id = add q ((p, TransitionLabel.Vis e)::path) in
                       (e, id)::acc
                     else
                       acc)
                   acc (channel_to_event_list ch))
            [] vists
        in
        let ts =
          List.map
            (fun (u, q) ->
              let id = add q ((p, TransitionLabel.Internal u)::path) in (u, id))
            tauts
        in
        r := (vs, ts, p#tick)
      done;
      ht

    let unfold channel_to_event_list p =
      let ht = unfold0 channel_to_event_list p in
      ht_to_lts ht p

  end
