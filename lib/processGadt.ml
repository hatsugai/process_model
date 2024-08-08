open Printf
open Transf

type ('e, 'ch) process =
  Process : {
      s : 'state;
      m : ('e, 'ch, 'state) process_interface;
    } -> ('e, 'ch) process

and ('e, 'ch, 'state) process_interface =
  {
      transf : 'state -> ('e, 'ch, 'state) sync_term list;
      show : 'state -> string;
      hash : 'state -> int;
      set : 'state -> unit;
      eq : 'state -> bool;
      mark : int list;
      mutable slot : 'state;
  }

let equal_process p q =
  match p with
    Process { s = p0; m = p_m } ->
    match q with
      Process { s = q0; m = q_m } ->
      p_m.mark == q_m.mark &&
        (p_m.set p0; q_m.eq q0)

let hash_process p =
  match p with Process { s; m } -> m.hash s

let show_process p =
  match p with Process { s; m } -> m.show s

let composition2 (type ev) (type ch)
      (module HT : Hashtbl.S with type key = ch)
      (event_to_ch : ev -> ch)
      (equal_event : ev -> ev -> bool)
      (sync : ch -> bool)
      (p : (ev, ch) process)
      (q : (ev, ch) process)
  =
  let module S =
    struct
      type 'state t =
        Send of ev * 'state
      | Recv of (ev -> bool) * (ev -> 'state)
    end
  in

  match p with
    Process { s = p0; m = p_m } ->
    match q with
      Process { s = q0; m = q_m } ->
      let show (p, q) = sprintf "(%s, %s)" (p_m.show p) (q_m.show q) in
      let hash (p, q) = (p_m.hash p) * 65537 + (q_m.hash q) in

      let rec m = { transf; show; hash; set; eq; slot = (p0, q0); 
                    mark = 0::(p_m.mark @ q_m.mark) }
      and set (p, q) = m.slot <- (p, q)
      and eq (p, q) =
        let (p', q') = m.slot in
        p_m.set p';
        q_m.set q';
        p_m.eq p && q_m.eq q

      and transf (p, q) =

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
                        S.Send (e1, p'), S.Send (e2, q') when equal_event e1 e2 ->
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

        scan (fun p -> (p, q)) (reg fst) p_m.transf p []
        |> scan (fun q -> (p, q)) (reg snd) q_m.transf q
        |> consensus ht (fun p q -> (p, q))
      in

      Process { s = (p0, q0); m }

let composition (type ev) (type ch)
      (module HT : Hashtbl.S with type key = ch)
      (event_to_ch : ev -> ch)
      (equal_event : ev -> ev -> bool)
      (sync : ch -> bool)
      (ps : (ev, ch) process list)
  =
  let n = List.length ps in
  let module S =
    struct
      type 'state t =
        Send of ev * 'state
      | Recv of (ev -> bool) * (ev -> 'state)
    end
  in

  let show ps =
    let f p = match p with Process { s; m } -> m.show s in
    match ps with
      [] -> "[]"
    | [p] -> "[" ^ f p ^ "]"
    | p::ps' ->
       (List.fold_left
          (fun acc p ->
            match p with
              Process { s; m } ->
              acc ^ "; " ^ m.show s)
          ("[" ^ f p) ps') ^ "]"
  in

  let hash ps = 
    let f acc p = match p with Process { s; m } -> acc * 17 + m.hash s in
    List.fold_left f 0 ps
  in

  let transf ps =
    let ht = HT.create 0 in
    let reg ch i t =
      let v =
        match HT.find_opt ht ch with
          Some v -> v
        | None ->
           let v = Array.make n [] in
           HT.add ht ch v; v
      in
      v.(i) <- t::v.(i)
    in

    let scan mk trans_list i p =
      match p with Process { s; m } ->
        let mk s = mk (Process { s; m }) in
        List.fold_left
          (fun trans_list syncterm ->
            match syncterm with
              Tau s -> Tau (mk s)::trans_list
            | Hidden (e, s) ->
               Hidden (e, mk s)::trans_list
            | Event (e, s) ->
               let ch = event_to_ch e in
               if sync ch then
                 (reg ch i (S.Send (e, Process { s; m })); trans_list)
               else
                 Event (e, mk s)::trans_list
            | Receive (ch, guard, targetf) ->
               if sync ch then
                 let tf e = Process { s = targetf e; m } in
                 reg ch i (S.Recv (guard, tf));
                 trans_list
               else
                 let tf e = mk (targetf e) in
                 Receive (ch, guard, tf)::trans_list)
          trans_list (m.transf s)
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
               if equal_event e e' then
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
         let mk p = List.rev_append rs (p::ps') in
         let trans_list = scan mk trans_list i p in
         loop trans_list (p::rs) (i+1) ps'
    in
    loop [] [] 0 ps
  in

  let rec m = { transf; show; hash; set; eq; slot = ps; mark = [n] }
  and set ps = m.slot <- ps
  and eq ps = List.for_all2 equal_process ps m.slot
  in
  Process { s = ps; m }

let interleave (ps : ('e, 'ch) process list) =
  let show ps =
    let f p = match p with Process { s; m } -> m.show s in
    match ps with
      [] -> "[]"
    | [p] -> "[" ^ (f p) ^ "]"
    | p::ps' ->
       let str =
         List.fold_left
           (fun acc p -> acc ^ "; " ^ (f p))
           (f p) ps'
       in
       "[" ^ str ^ "]"
  in
  let hash ps =
    let f acc p = match p with Process { s; m } -> acc * 17 + m.hash s in
    List.fold_left f 0 ps
  in
  let rec m = { transf; show; hash; set; eq; slot = ps;
                mark = [List.length ps] }
  and set ps = m.slot <- ps
  and eq ps = List.for_all2 equal_process ps m.slot
  and transf ps =
    let rec loop acc rs ps =
      match ps with
        [] -> acc
      | p::ps' ->
         (match p with Process { s; m } ->
            let mk s = List.rev_append rs (Process { s; m }::ps') in
            let acc =
              List.fold_left (fun acc syterm ->
                  match syterm with
                    Tau s' -> Tau (mk s')::acc
                  | Event (e, s') -> Event (e, (mk s'))::acc
                  | Hidden (e, s') -> Hidden (e, (mk s'))::acc
                  | Receive (ch, g, tf) ->
                     let tf' e = mk (tf e) in
                     Receive (ch, g, tf')::acc)
                acc (m.transf s)
            in
            loop acc (p::rs) ps')
    in
    loop [] [] ps
  in
  Process { s = ps; m }
