open Type

exception Error

type ('event, 'channel, 'state) sync_term =
  Tau of 'state
| Event of 'event * 'state
| Receive of 'channel * ('event -> bool) * ('event -> 'state)
| Hidden of 'event * 'state

module type StateType =
  sig
    type t
    val show : t -> string
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int
  end

let guard_true _ = true

let hide event_to_ch pred transf state =
  List.map (fun syncterm ->
      match syncterm with
        Event (e, s) ->
         let ch = event_to_ch e in
         if pred ch then
           Hidden (e, s)
         else
           Event (e, s)
      | Tau _ | Hidden _ | Receive _ -> syncterm)
    (transf state)

let enlist_process transf state =
  match state with
    [s] ->
     List.map (fun syncterm ->
         match syncterm with
           Tau s -> Tau [s]
         | Event (e, s) -> Event (e, [s])
         | Hidden (e, s) -> Event (e, [s])
         | Receive (ch, g, targetf) ->
            Receive (ch, g, (fun e -> [targetf e])))
       (transf s)
  | _ -> raise Error


module Composition (E : EventType) (C : ChannelType) =
  struct

    module CHT = Hashtbl.Make (C)

    let reg ht sel ch term =
      let r =
        sel (match CHT.find_opt ht ch with
               None ->
                let pair = (ref [], ref []) in
                CHT.add ht ch pair;
                pair
             | Some pair -> pair)
      in
      r := term::!r

    let scan event_to_ch sync mkpair reg transf s trans_list =
      List.fold_left
        (fun trans_list syncterm ->
          match syncterm with
            Tau s -> Tau (mkpair s)::trans_list
          | Hidden (e, s) ->
             Hidden (e, mkpair s)::trans_list
          | Event (e, s) ->
             let ch = event_to_ch e in
             if sync ch then
               (reg ch syncterm; trans_list)
             else
               Event (e, mkpair s)::trans_list
          | Receive (ch, guard, targetf) ->
             if sync ch then
               (reg ch syncterm; trans_list)
             else
               let targetf' e = mkpair (targetf e) in
               Receive (ch, guard, targetf')::trans_list)
        trans_list (transf s)

    let consensus ht mkpair trans_list =
      CHT.fold
        (fun _chid (ps, qs) trans_list ->
          List.fold_left
            (fun trans_list pterm ->
              List.fold_left
                (fun trans_list qterm ->
                  match pterm, qterm with
                    Event (e1, p'), Event (e2, q') when E.equal e1 e2 ->
                     Event (e1, mkpair p' q')::trans_list
                  | Event (e, p'), Receive (_ch, guard, targetf) when guard e ->
                     Event (e, mkpair p' (targetf e))::trans_list
                  | Receive (_ch, guard, targetf), Event (e, q') when guard e ->
                     Event (e, mkpair (targetf e) q')::trans_list
                  | Receive (ch, g1, tf1), Receive (_, g2, tf2) ->
                     let guard e = g1 e && g2 e in
                     let targetf e = mkpair (tf1 e) (tf2 e) in
                     (Receive (ch, guard, targetf))::trans_list
                  | _, _ -> trans_list)
                trans_list !qs)
            trans_list !ps)
        ht trans_list

    let composition event_to_ch sync ptransf qtransf (p, q) =
      let ht = CHT.create 0 in
      scan event_to_ch sync (fun p -> (p, q)) (reg ht fst) ptransf p []
      |> scan event_to_ch sync (fun q -> (p, q)) (reg ht snd) qtransf q
      |> consensus ht (fun p q -> (p, q))

    let composition2 event_to_ch sync ptransf qtransf ps =
      let ht = CHT.create 0 in
      match ps with
        [] -> raise Error
      | p::q ->
         scan event_to_ch sync (fun p -> p::q) (reg ht fst) ptransf p []
         |> scan event_to_ch sync (fun q -> p::q) (reg ht snd) qtransf q
         |> consensus ht (fun p q -> p::q)

    let interleave transf_list ps =
      let rec loop trans_list tfs rs ps =
        match tfs, ps with
          [], [] -> trans_list
        | tf::tfs', p::ps' ->
           let trans_list =
             List.fold_left
               (fun trans_list syncterm ->
                 match syncterm with
                   Tau s -> Tau (List.rev_append rs (s::ps'))::trans_list
                 | Hidden (e, s) ->
                    Hidden (e, List.rev_append rs (s::ps'))::trans_list
                 | Event (e, s) ->
                    Event (e, List.rev_append rs (s::ps'))::trans_list
                 | Receive (ch, guard, targetf) ->
                    let targetf' e = List.rev_append rs (targetf e::ps') in
                    Receive (ch, guard, targetf')::trans_list)
               trans_list (tf p)
           in
           loop trans_list tfs' (p::rs) ps'
        | _, _ -> raise Error
      in
      loop [] transf_list [] ps

    let interleave2 transf ps =
      interleave (List.map (fun _ -> transf) ps) ps

  end
