open Type
open Transf

module Make (E : EventType) (C : ChannelType) =
  struct
    type 'state process_intreface = {
        transf : 'state -> (E.t, C.t, 'state) sync_term list;
        mark : int list;
        eq : 'state -> bool;
        set : 'state -> unit;
        hash : 'state -> int;
        show : 'state -> string;
        mutable slot : 'state;
      }

    module type PROCESS =
      sig
        type t
        val m : t process_intreface
        val state : t
      end

    let equal_process p q =
      let module P = (val p : PROCESS) in
      let module Q = (val q : PROCESS) in
      P.m.mark == Q.m.mark
      && (P.m.set P.state; Q.m.eq Q.state)

    let hash_process p =
      let module P = (val p : PROCESS) in
      P.m.hash P.state

    let show_process p =
      let module P = (val p : PROCESS) in
      P.m.show P.state

    module HT = Hashtbl.Make (C)

    let composition
          (event_to_ch : E.t -> C.t)
          (sync : C.t -> bool)
          (ps : (module PROCESS) list)
      =
      let module S =
        struct
          type t =
            Send of E.t * (module PROCESS)
          | Recv of (E.t -> bool) * (E.t -> (module PROCESS))
        end
      in

      let n = List.length ps in

      let transf ps =
        let ht = HT.create 0 in

        let reg ch i term =
          let v =
            match HT.find_opt ht ch with
              None ->
               let v = Array.make n [] in
               HT.add ht ch v;
               v
            | Some v -> v
          in
          v.(i) <- term::v.(i);
        in

        let consensus ch ys =

          let rec loop_ev e rs ys =
            match ys with
              [] ->
               let qs = List.rev rs in
               Some (Event (e, qs))
            | y::ys' ->
               (match y with
                  S.Send (e', q) ->
                   if E.equal e e' then
                     loop_ev e (q::rs) ys'
                   else
                     None
                | S.Recv (g, tf) ->
                   if g e then
                     loop_ev e ((tf e)::rs) ys'
                   else
                     None)

          and loop_recv gs rs ys =
            match ys with
              [] ->
               let ts = List.rev rs in
               Some (Receive (ch,
                              (fun e -> List.for_all (fun g -> g e) gs),
                              (fun e ->
                                let qs = List.map (fun tf -> tf e) ts in
                                qs)))
            | y::ys' ->
               (match y with
                  S.Send (e, q) ->
                   if List.for_all (fun g -> g e) gs then
                     loop_ev e (q::(List.map (fun tf -> tf e) rs)) ys'
                   else
                     None
                | Recv (g, tf) ->
                   loop_recv (g::gs) (tf::rs) ys')
          in

          match ys with
            [] -> Error.f "composition: no processes"
          | y::ys' ->
             (match y with
              | S.Send (e, q) -> loop_ev e [q] ys'
              | S.Recv (g, tf) -> loop_recv [g] [tf] ys')
        in

        let sync_trans trans_list =
          HT.fold
            (fun ch v trans_list ->
              let xss = Array.to_list v in
              let yss = Util.cartesian_product xss in
              List.fold_left
                (fun trans_list ys ->
                  match consensus ch ys with
                    None -> trans_list
                  | Some t -> t::trans_list)
                trans_list yss)
            ht trans_list
        in

        let rec loop trans_list rs i ps =
          match ps with
            [] -> sync_trans trans_list
          | p::ps' ->
             let module P = (val p : PROCESS) in
             let mkmod s =
               (module (struct
                         type t = P.t
                         let m = P.m
                         let state = s
                       end) : PROCESS)
             in
             let trans_list =
               List.fold_left
                 (fun trans_list syncterm ->
                   match syncterm with
                     Tau s ->
                      Tau (List.rev_append rs (mkmod s::ps'))::trans_list
                   | Hidden (e, s) ->
                      Hidden (e, List.rev_append rs (mkmod s::ps'))::trans_list
                   | Event (e, s) ->
                      let ch = event_to_ch e in
                      if sync ch then
                        (reg ch i (Send (e, mkmod s)); trans_list)
                      else
                        Event (e, List.rev_append rs (mkmod s::ps'))::trans_list
                   | Receive (ch, guard, targetf) ->
                      if sync ch then
                        let tf e = mkmod (targetf e) in
                        reg ch i (Recv (guard, tf));
                        trans_list
                      else
                        let targetf' e =
                          List.rev_append rs (mkmod (targetf e)::ps')
                        in
                        Receive (ch, guard, targetf')::trans_list)
                 trans_list (P.m.transf P.state)
             in
             loop trans_list (p::rs) (i+1) ps'
        in
        loop [] [] 0 ps
      in

      let hash ps =
        List.fold_left
          (fun acc p ->
            let module P = (val p : PROCESS) in
            acc * 17 + P.m.hash P.state)
          0 ps
      in

      let show ps =
        List.fold_left
          (fun acc p ->
            let module P = (val p : PROCESS) in
            acc ^ (P.m.show P.state))
          "" ps
      in

      let rec m = { transf; mark = [0]; eq; set; hash; show; slot = ps }
      and set ps = m.slot <- ps
      and eq ps =
        List.for_all2
          (fun p q ->
            let module P = (val p : PROCESS) in
            let module Q = (val q : PROCESS) in
            P.m.mark == Q.m.mark
            && (P.m.set P.state; Q.m.eq Q.state))
          ps m.slot
      in

      (module (struct
                type t = (module PROCESS) list
                let m = m
                let state = ps
              end) : PROCESS)

    let composition2
          (event_to_ch : E.t -> C.t)
          (sync : C.t -> bool)
          (p : (module PROCESS))
          (q : (module PROCESS))
      =
      let module S =
        struct
          type 'state t =
            Send of E.t * 'state
          | Recv of (E.t -> bool) * (E.t -> 'state)
        end
      in

      let module P = (val p : PROCESS) in
      let module Q = (val q : PROCESS) in

      let transf (p, q) =
        let ht = HT.create 0 in

        let reg sel ch term =
          let r =
            sel (match HT.find_opt ht ch with
                   None ->
                    let pair = (ref [], ref []) in
                    HT.add ht ch pair;
                    pair
                 | Some pair -> pair)
          in
          r := term::!r
        in

        let scan mkpair reg transf p trans_list =
          List.fold_left
            (fun trans_list syncterm ->
              match syncterm with
                Tau s -> Tau (mkpair s)::trans_list
              | Hidden (e, s) ->
                 Hidden (e, mkpair s)::trans_list
              | Event (e, s) ->
                 let ch = event_to_ch e in
                 if sync ch then
                   (reg ch (S.Send (e, s)); trans_list)
                 else
                   Event (e, mkpair s)::trans_list
              | Receive (ch, guard, targetf) ->
                 if sync ch then
                   (reg ch (Recv (guard, targetf)); trans_list)
                 else
                   let targetf' e = mkpair (targetf e) in
                   Receive (ch, guard, targetf')::trans_list)
            trans_list (transf p)
        in

        let consensus ht mkpair trans_list =
          HT.fold
            (fun ch (ps, qs) trans_list ->
              List.fold_left
                (fun trans_list pterm ->
                  List.fold_left
                    (fun trans_list qterm ->
                      match pterm, qterm with
                        S.Send (e1, p'), S.Send (e2, q') when E.equal e1 e2 ->
                         Event (e1, mkpair p' q')::trans_list
                      | S.Send (e, p'), S.Recv (guard, targetf) when guard e ->
                         Event (e, mkpair p' (targetf e))::trans_list
                      | S.Recv (guard, targetf), S.Send (e, q') when guard e ->
                         Event (e, mkpair (targetf e) q')::trans_list
                      | S.Recv (g1, tf1), S.Recv (g2, tf2) ->
                         let guard e = g1 e && g2 e in
                         let targetf e = mkpair (tf1 e) (tf2 e) in
                         (Receive (ch, guard, targetf))::trans_list
                      | _, _ -> trans_list)
                    trans_list !qs)
                trans_list !ps)
            ht trans_list
        in

        scan (fun p -> (p, q)) (reg fst) P.m.transf p []
        |> scan (fun q -> (p, q)) (reg snd) Q.m.transf q
        |> consensus ht (fun p q -> (p, q))
      in

      let hash (p, q) =
        (P.m.hash p) * 65537 + (Q.m.hash q)
      in

      let show (p, q) =
        "(" ^ (P.m.show p) ^ ", " ^ (Q.m.show q) ^ ")"
      in

      let rec m = { transf; eq; set; hash; show;
                    mark = [0]; slot = (P.state, Q.state) }
      and set (p, q) = m.slot <- (p, q)
      and eq (p, q) =
        let (p', q') = m.slot in
        (P.m.set p; P.m.eq p') && (Q.m.set q; Q.m.eq q')
      in

      (module (struct
                type t = P.t * Q.t
                let m = m
                let state = (P.state, Q.state)
              end) : PROCESS)

  end
