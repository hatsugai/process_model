open Type

module Make (E : EventType) =
  struct

    module L = TransitionLabel

    module EHT = Hashtbl.Make (E)

    module SSHT =
      Lockfree_hashtable.Make (
          struct
            type t = Intset.t
            let equal = Intset.equal
            let hash = Intset.hash
          end)

    let tau_closure tau_transv ss =
      let que = Queue.create () in
      Intset.iter (fun s -> Queue.add s que) ss;
      while not (Queue.is_empty que) do
        let s = Queue.take que in
        let ts = tau_transv.(s) in
        List.iter
          (fun (_, q) ->
            if not (Intset.mem q ss) then
              (Queue.add q que; Intset.add q ss))
          ts;
      done

    let ht_update ht e t =
      match EHT.find_opt ht e with
        None ->
         let ss = Intset.make () in
         Intset.add t ss;
         EHT.add ht e ss
      | Some ss ->
         Intset.add t ss

    type det_branches = {
        mutable ssid : int;
        mutable transitions : (E.t * int) list;
      }

    let det ?(b_progress = false) num_workers ht_size chunk_size vv vt =

      let ssht = SSHT.create ht_size in
      let next_ssid = Atomic.make 1 in

      let do_work xc =

        let collect_transitions ss =
          let eht = EHT.create 0 in
          Intset.iter
            (fun s ->
              List.iter
                (fun (e, t) -> ht_update eht e t)
                vv.(s))
            ss;
          EHT.fold
            (fun e tt trans ->
              tau_closure vt tt;
              let br = { ssid = Atomic.get next_ssid; transitions = [] } in
              let (b_new, tt2, br2) = SSHT.add ssht tt br in
              if b_new then
                let ssid = Atomic.fetch_and_add next_ssid 1 in
                br.ssid <- ssid;
                Parstep.put xc (tt2, br);
                (e, ssid)::trans
              else
                (e, br2.ssid)::trans)
            eht []
        in

        let rec loop () =
          match Parstep.get xc with
            None -> ()
          | Some (ss, br) ->
             br.transitions <- collect_transitions ss;
             loop ()
        in
        loop ()
      in
      
      let ss0 = Intset.make () in
      Intset.add 0 ss0;
      tau_closure vt ss0;
      let br = { ssid = 0; transitions = [] } in
      let _ = SSHT.add ssht ss0 br in
      Parstep.parstep ~b_progress num_workers chunk_size (ss0, br) do_work;
      Printf.printf "max_chain_length: %d\n" (SSHT.max_chain_length ssht);
      Printf.printf "conflicts: %d\n" (Atomic.get ssht.c);
      (ss0, ssht)

    let ssht_to_vec_par num_workers ssht ss0 =
      let n = Atomic.get ssht.SSHT.n in
      let vs = Array.make n ss0 in
      let vv = Array.make n [] in
      SSHT.par_iter num_workers
        (fun state (br : det_branches) ->
          let i = br.ssid in
          if not (0 <= i && i < n) then
            (Printf.printf "%d %d\n" i n; flush stdout);
          assert (0 <= i && i < n);
          assert (vs.(i) == ss0);
          vs.(i) <- state;
          vv.(i) <- br.transitions)
        ssht;
      for i=1 to n-1 do
        assert (vs.(i) != ss0)
      done;
      (vs, vv)

    module IntPair =
      struct
        type t = int * int
        let equal (p1, q1) (p2, q2) = p1 = p2 && q1 = q2
        let hash (p, q) = p + q * 104729
      end

    module PHT = Lockfree_hashtable.Make (IntPair)

    type check_traces_result =
      CT_Violation of E.t * (E.t L.revent * (int * int)) list
    | CT_Ok of bool PHT.t

    let check_traces ?(b_progress = false) num_workers ht_size chunk_size
          dvv ivv ivt =
      let violation = Atomic.make None in
      let ht = PHT.create ht_size in
      let do_work xc =
        let add pq path =
          let (b_new, pq2, _) = PHT.add ht pq true in
          if b_new then
            Parstep.put xc (pq2, path)
        in
        let rec loop () =
          match Parstep.get xc with
            None -> ()
          | Some ((p, q), path) ->
             List.iter
               (fun (i, q') ->
                 add (p, q') ((L.Internal i, (p, q'))::path))
               ivt.(q);
             let p_trans = dvv.(p) in
             let rec scan eqs =
               match eqs with
                 [] -> loop ()
               | (e, q')::eqs' ->
                  match List.assoc_opt e p_trans with
                    None ->
                     Parstep.abort xc;
                     let _ = Atomic.compare_and_set violation None
                               (Some (CT_Violation (e, path)))
                     in

                     ()
                  | Some p' ->
                     add (p', q') ((L.Vis e, (p', q'))::path);
                     scan eqs'
             in
             scan ivv.(q);
        in
        add (0, 0) [];
        loop ()
      in
      let pq0 = (0, 0) in
      let _ = PHT.add ht pq0 true in
      Parstep.parstep ~b_progress num_workers chunk_size
        (pq0, [(L.Internal Tau, pq0)]) do_work;
      Printf.printf "max_chain_length: %d\n" (PHT.max_chain_length ht);
      Printf.printf "conflicts: %d\n" (Atomic.get ht.c);
      match Atomic.get violation with
        Some v -> v
      | None -> CT_Ok ht

    module ES = Set.Make (E)

    module ESS =
      Set.Make (
          struct
            type t = ES.t
            let compare = ES.compare
          end)

    let stable_state_initials vv q =
      List.fold_left
        (fun s (e, _) -> ES.add e s)
        ES.empty vv.(q)

    let minaccs_of_ss vv vt ss =
      Intset.fold
        (fun s acc ->
          if vt.(s) = [] then
            let initials = stable_state_initials vv s in
            ESS.add initials acc
          else
            acc)
        ss ESS.empty

    let min_acceptances num_workers vv vt dvs =
      let n = Array.length dvs in
      let vaccs = Array.make n ESS.empty in
      Par_iter.par_iter num_workers n
        (fun start end_1 ->
          for i = start to end_1 do
            vaccs.(i) <- minaccs_of_ss vv vt dvs.(i)
          done);
      vaccs

    let check_refusals spec_acceptances ivv ivt q =
      if ivt.(q) = [] then
        let initials = stable_state_initials ivv q in
        if ESS.exists
             (fun spec_acc -> ES.subset spec_acc initials)
             spec_acceptances
        then
          None
        else
          Some initials
      else
        None

    type check_failures_result =
      CF_TraceViolation of E.t * (E.t L.revent * (int * int)) list
    | CF_RefusalViolation of ESS.t * ES.t * int * int * (E.t L.revent * (int * int)) list
    | CF_Ok of bool PHT.t

    let check_failures ?(b_progress = false) num_workers ht_size chunk_size
          dvv vaccs ivv ivt =
      let violation = Atomic.make None in
      let ht = PHT.create ht_size in
      let do_work xc =
        let add pq path =
          let (b_new, pq2, _) = PHT.add ht pq true in
          if b_new then
            Parstep.put xc (pq2, path)
        in
        let rec loop () =
          match Parstep.get xc with
            None -> ()
          | Some ((p, q), path) ->

          match check_refusals vaccs.(p) ivv ivt q with
            Some initials ->
             Parstep.abort xc;
             let _ = Atomic.compare_and_set violation None
                       (Some (CF_RefusalViolation (vaccs.(p), initials, p, q, path)))
             in
             ()
          | None ->
             List.iter
               (fun (i, q') ->
                 add (p, q') ((L.Internal i, (p, q'))::path))
               ivt.(q);
             let p_trans = dvv.(p) in
             let rec scan eqs =
               match eqs with
                 [] -> loop ()
               | (e, q')::eqs' ->
                  match List.assoc_opt e p_trans with
                    None ->
                     Parstep.abort xc;
                     let _ = Atomic.compare_and_set violation None
                               (Some (CF_TraceViolation (e, path)))
                     in

                     ()
                  | Some p' ->
                     add (p', q') ((L.Vis e, (p', q'))::path);
                     scan eqs'
             in
             scan ivv.(q);
        in
        add (0, 0) [];
        loop ()
      in
      let pq0 = (0, 0) in
      let _ = PHT.add ht pq0 true in
      Parstep.parstep ~b_progress num_workers chunk_size
        (pq0, [(L.Internal Tau, pq0)]) do_work;
      Printf.printf "max_chain_length: %d\n" (PHT.max_chain_length ht);
      Printf.printf "conflicts: %d\n" (Atomic.get ht.c);
      match Atomic.get violation with
        Some vio -> vio
      | None -> CF_Ok ht

  end

module Make1 (E : EventType) =
  struct

    module L = TransitionLabel

    module EHT = Hashtbl.Make (E)

    module SSHT =
      Hashtbl.Make (
          struct
            type t = Intset.t
            let equal = Intset.equal
            let hash = Intset.hash
          end)

    let tau_closure tau_transv ss =
      let que = Queue.create () in
      Intset.iter (fun s -> Queue.add s que) ss;
      while not (Queue.is_empty que) do
        let s = Queue.take que in
        let ts = tau_transv.(s) in
        List.iter
          (fun (_, q) ->
            if not (Intset.mem q ss) then
              (Queue.add q que; Intset.add q ss))
          ts;
      done

    let ht_update ht e t =
      match EHT.find_opt ht e with
        None ->
         let ss = Intset.make () in
         Intset.add t ss;
         EHT.add ht e ss
      | Some ss ->
         Intset.add t ss

    type det_branches = {
        ssid : int;
        mutable transitions : (E.t * int) list;
      }

    let det ht_size vv vt =

      let ssht = SSHT.create ht_size in
      let que = Queue.create () in

      let add tt =
        match SSHT.find_opt ssht tt with
          None ->
           let br = { ssid = SSHT.length ssht; transitions = [] } in
           SSHT.replace ssht tt br;
           Queue.add (tt, br) que;
           br.ssid
        | Some br ->
           br.ssid
      in

      let collect_transitions ss =
        let eht = EHT.create 0 in
        Intset.iter
          (fun s ->
            List.iter
              (fun (e, t) -> ht_update eht e t)
              vv.(s))
          ss;
        EHT.fold
          (fun e tt trans ->
            tau_closure vt tt;
            let ssid = add tt in
            (e, ssid)::trans)
          eht []
      in
      
      let ss0 = Intset.make () in
      Intset.add 0 ss0;
      tau_closure vt ss0;
      let br = { ssid = 0; transitions = [] } in
      let _ = SSHT.add ssht ss0 br in

      while not (Queue.is_empty que) do
        let (ss, br) = Queue.take que in
        br.transitions <- collect_transitions ss;
      done;

      (ss0, ssht)

    let ssht_to_vec ssht ss0 =
      let n = SSHT.length ssht in
      let vs = Array.make n ss0 in
      let vv = Array.make n [] in
      SSHT.iter
        (fun state (br : det_branches) ->
          let i = br.ssid in
          if not (0 <= i && i < n) then
            (Printf.printf "%d %d\n" i n; flush stdout);
          assert (0 <= i && i < n);
          assert (vs.(i) == ss0);
          vs.(i) <- state;
          vv.(i) <- br.transitions)
        ssht;
      for i=1 to n-1 do
        assert (vs.(i) != ss0)
      done;
      (vs, vv)

    module IntPair =
      struct
        type t = int * int
        let equal (p1, q1) (p2, q2) = p1 = p2 && q1 = q2
        let hash (p, q) = p + q * 104729
      end

    module PHT = Hashtbl.Make (IntPair)

    type check_traces_result =
      CT_Violation of E.t * (E.t L.revent * (int * int)) list
    | CT_Ok of bool PHT.t

    let check_traces ht_size dvv ivv ivt =
      let ht = PHT.create ht_size in
      let que = Queue.create () in

      let add pq path =
        if not (PHT.mem ht pq) then
          (PHT.add ht pq true;
           Queue.add (pq, path) que)
      in

      let rec loop () =
        if Queue.is_empty que then
          CT_Ok ht
        else
          let ((p, q), path) = Queue.take que in
          List.iter
            (fun (i, q') ->
              add (p, q') ((L.Internal i, (p, q'))::path))
            ivt.(q);
          let p_trans = dvv.(p) in
          let rec scan eqs =
            match eqs with
              [] -> loop ()
            | (e, q')::eqs' ->
               match List.assoc_opt e p_trans with
                 None ->
                 CT_Violation (e, path)
               | Some p' ->
                  add (p', q') ((L.Vis e, (p', q'))::path);
                  scan eqs'
          in
          scan ivv.(q);
      in
      add (0, 0) [];
      loop ()

    module ES = Set.Make (E)

    module ESS =
      Set.Make (
          struct
            type t = ES.t
            let compare = ES.compare
          end)

    let stable_state_initials vv q =
      List.fold_left
        (fun s (e, _) -> ES.add e s)
        ES.empty vv.(q)

    let minaccs_of_ss vv vt ss =
      Intset.fold
        (fun s acc ->
          if vt.(s) = [] then
            let initials = stable_state_initials vv s in
            ESS.add initials acc
          else
            acc)
        ss ESS.empty

    let min_acceptances vv vt dvs =
      let n = Array.length dvs in
      let vaccs = Array.make n ESS.empty in
      for i = 0 to n - 1 do
        vaccs.(i) <- minaccs_of_ss vv vt dvs.(i)
      done;
      vaccs

    let check_refusals spec_acceptances ivv ivt q =
      if ivt.(q) = [] then
        let initials = stable_state_initials ivv q in
        if ESS.exists
             (fun spec_acc -> ES.subset spec_acc initials)
             spec_acceptances
        then
          None
        else
          Some initials
      else
        None

    type check_failures_result =
      CF_TraceViolation of E.t * (E.t L.revent * (int * int)) list
    | CF_RefusalViolation of ESS.t * ES.t * int * int * (E.t L.revent * (int * int)) list
    | CF_Ok of bool PHT.t

    let check_failures ht_size dvv vaccs ivv ivt =
      let ht = PHT.create ht_size in
      let que = Queue.create () in

      let add pq path =
        if not (PHT.mem ht pq) then
          (PHT.add ht pq true;
           Queue.add (pq, path) que)
      in

      let rec loop () =
        if Queue.is_empty que then
          CF_Ok ht
        else
          let ((p, q), path) = Queue.take que in
          match check_refusals vaccs.(p) ivv ivt q with
            Some initials ->
             CF_RefusalViolation (vaccs.(p), initials, p, q, path)
          | None ->
             List.iter
               (fun (i, q') ->
                 add (p, q') ((L.Internal i, (p, q'))::path))
               ivt.(q);
             let p_trans = dvv.(p) in
             let rec scan eqs =
               match eqs with
                 [] -> loop ()
               | (e, q')::eqs' ->
                  match List.assoc_opt e p_trans with
                    None ->
                     CF_TraceViolation (e, path)
                  | Some p' ->
                     add (p', q') ((L.Vis e, (p', q'))::path);
                     scan eqs'
             in
             scan ivv.(q);
      in
      add (0, 0) [];
      loop ()

  end
