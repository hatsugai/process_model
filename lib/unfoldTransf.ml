open Type
open Transf

module Make (E : EventType) (S : StateType) =
  struct

    module L = TransitionLabel

    module HT1 = Hashtbl.Make (S)

    type branches1 = {
        state_id : int;
        mutable vis_transitions : (E.t * int) list;
        mutable tau_transitions : (E.t L.ievent * int) list;
      }

    let make_branches1 state_id = {
        state_id;
        vis_transitions = [];
        tau_transitions = [];
      }

    let unfold1 ht_size channel_to_event_list transf s0 =
      let ht = HT1.create ht_size in
      let que = Queue.create () in

      let collect_receive_transitions vs ts ch guard targetf =
        let rec loop vs ts es =
          match es with
            [] -> (vs, ts)
          | e::es' ->
             if guard e then
               let target = targetf e in
               match HT1.find_opt ht target with
                 None ->
                  let br = make_branches1 (HT1.length ht) in
                  HT1.add ht target br;
                  Queue.add (target, br) que;
                  loop ((e, br.state_id)::vs) ts es'
               | Some br ->
                  loop ((e, br.state_id)::vs) ts es'
             else
               loop vs ts es'
        in
        loop vs ts (channel_to_event_list ch)
      in

      let collect_transitions state =
        let rec loop vs ts trans_list =
          match trans_list with
            [] -> (vs, ts)
          | syncterm::trans_list' ->
             (match syncterm with
                Tau target ->
                 (match HT1.find_opt ht target with
                    None ->
                     let br = make_branches1 (HT1.length ht) in
                     HT1.add ht target br;
                     Queue.add (target, br) que;
                     loop vs ((L.Tau, br.state_id)::ts) trans_list'
                  | Some br ->
                     loop vs ((L.Tau, br.state_id)::ts) trans_list')
              | Event (event, target) ->
                 (match HT1.find_opt ht target with
                    None ->
                     let br = make_branches1 (HT1.length ht) in
                     HT1.add ht target br;
                     Queue.add (target, br) que;
                     loop ((event, br.state_id)::vs) ts trans_list'
                  | Some br ->
                     loop ((event, br.state_id)::vs) ts trans_list')
              | Hidden (event, target) ->
                 (match HT1.find_opt ht target with
                    None ->
                     let br = make_branches1 (HT1.length ht) in
                     HT1.add ht target br;
                     Queue.add (target, br) que;
                     loop vs ((L.Hid event, br.state_id)::ts) trans_list'
                  | Some br ->
                     loop vs ((L.Hid event, br.state_id)::ts) trans_list')
              | Receive (ch, guard, targetf) ->
                 let (vs, ts) = collect_receive_transitions vs ts ch guard targetf in
                 loop vs ts trans_list')
        in
        loop [] [] (transf state)
      in

      let rec loop () =
        if Queue.is_empty que then
          ()
        else
          let (state, br) = Queue.take que in
          let (vs, ts) = collect_transitions state in
          br.vis_transitions <- vs;
          br.tau_transitions <- ts;
          loop ()
      in

      let br = make_branches1 0 in
      HT1.add ht s0 br;
      Queue.add (s0, br) que;
      loop ();
      Printf.printf "%d\n" (HT1.length ht);
      ht

    type branches = {
        state_id : int Atomic.t;
        mutable vis_transitions : (E.t * int) list;
        mutable tau_transitions : (E.t L.ievent * int) list;
      }

    let make_branches () = {
        state_id = Atomic.make (-1);
        vis_transitions = [];
        tau_transitions = [];
      }

    module HT = Lockfree_hashtable.Make (S)

    let rec spin_wait a x =
      let y = Atomic.get a in
      if x = y then
        (Domain.cpu_relax (); spin_wait a x)
      else
        y

    let unfold ?(b_progress = false) num_workers ht_size chunk_size
          channel_to_event_list transf s0 =

      let next_state_id = Atomic.make 1 in

      let do_work ht transf (xc : 'a Parstep.worker_context) =

        let collect_receive_transitions br vs ts ch guard targetf =
          let rec loop br vs ts es =
            match es with
              [] -> (br, vs, ts)
            | e::es' ->
               if guard e then
                 let target = targetf e in
                 let (b_new, _, br2) = HT.add ht target br in
                 if b_new then
                   let state_id = Atomic.fetch_and_add next_state_id 1 in
                   Atomic.set br.state_id state_id;
                   Parstep.put xc (target, br);
                   let br = make_branches () in
                   loop br ((e, state_id)::vs) ts es'
                 else
                   let state_id = spin_wait br2.state_id (-1) in
                   loop br ((e, state_id)::vs) ts es'
               else
                 loop br vs ts es'
          in
          loop br vs ts (channel_to_event_list ch)
        in

        let collect_transitions state br =
          let rec loop br vs ts trans_list =
            match trans_list with
              [] -> (br, vs, ts)
            | syncterm::trans_list' ->
               (match syncterm with
                  Tau target ->
                   let (b_new, _, br2) = HT.add ht target br in
                   if b_new then
                     let state_id = Atomic.fetch_and_add next_state_id 1 in
                     Atomic.set br.state_id state_id;
                     Parstep.put xc (target, br);
                     let br = make_branches () in
                     loop br vs ((L.Tau, state_id)::ts) trans_list'
                   else
                     let state_id = spin_wait br2.state_id (-1) in
                     loop br vs ((L.Tau, state_id)::ts) trans_list'
                | Event (event, target) ->
                   let (b_new, _, br2) = HT.add ht target br in
                   if b_new then
                     let state_id = Atomic.fetch_and_add next_state_id 1 in
                     Atomic.set br.state_id state_id;
                     Parstep.put xc (target, br);
                     let br = make_branches () in
                     loop br ((event, state_id)::vs) ts trans_list'
                   else
                     let state_id = spin_wait br2.state_id (-1) in
                     loop br ((event, state_id)::vs) ts trans_list'
                | Hidden (event, target) ->
                   let (b_new, _, br2) = HT.add ht target br in
                   if b_new then
                     let state_id = Atomic.fetch_and_add next_state_id 1 in
                     Atomic.set br.state_id state_id;
                     Parstep.put xc (target, br);
                     let br = make_branches () in
                     loop br vs ((Hid event, state_id)::ts) trans_list'
                   else
                     let state_id = spin_wait br2.state_id (-1) in
                     loop br vs ((Hid event, state_id)::ts) trans_list'
                | Receive (ch, guard, targetf) ->
                   let (br, vs, ts) = collect_receive_transitions br vs ts ch guard targetf in
                   loop br vs ts trans_list')
          in
          loop br [] [] (transf state)
        in

        let rec loop br =
          match Parstep.get xc with
            None -> ()
          | Some (state, branches) ->
             let (br, vs, ts) = collect_transitions state br in
             branches.vis_transitions <- vs;
             branches.tau_transitions <- ts;
             loop br

        in
        loop (make_branches ())
      in

      let ht = HT.create ht_size in
      let br = make_branches () in
      Atomic.set br.state_id 0;
      let _ = HT.add ht s0 br in
      Parstep.parstep ~b_progress num_workers chunk_size (s0, br)
        (do_work ht transf);
      Printf.printf "max_chain_length: %d\n" (HT.max_chain_length ht);
      Printf.printf "conflicts: %d\n" (Atomic.get ht.c);
      ht

    let check_deadlock ?(b_progress = false) num_workers ht_size chunk_size
          channel_to_event_list transf s0 =

      let next_state_id = Atomic.make 1 in
      let deadlock_path : (E.t L.revent * S.t) list option Atomic.t = Atomic.make None in

      let do_work ht transf (xc : (S.t * (E.t L.revent * S.t) list * branches) Parstep.worker_context) =

        let collect_receive_transitions path br vs ts ch guard targetf =
          let rec loop br vs ts es =
            match es with
              [] -> (br, vs, ts)
            | e::es' ->
               if guard e then
                 let target = targetf e in
                 let (b_new, target2, br2) = HT.add ht target br in
                 if b_new then
                   let state_id = Atomic.fetch_and_add next_state_id 1 in
                   Atomic.set br.state_id state_id;
                   Parstep.put xc (target, (Vis e, target2)::path, br);
                   let br = make_branches () in
                   loop br ((e, state_id)::vs) ts es'
                 else
                   let state_id = spin_wait br2.state_id (-1) in
                   loop br ((e, state_id)::vs) ts es'
               else
                 loop br vs ts es'
          in
          loop br vs ts (channel_to_event_list ch)
        in

        let collect_transitions path br trans_list =
          let rec loop br vs ts trans_list =
            match trans_list with
              [] -> (br, vs, ts)
            | syncterm::trans_list' ->
               (match syncterm with
                  Tau target ->
                   let (b_new, target2, br2) = HT.add ht target br in
                   if b_new then
                     let state_id = Atomic.fetch_and_add next_state_id 1 in
                     Atomic.set br.state_id state_id;
                     Parstep.put xc (target, (Internal Tau, target2)::path, br);
                     let br = make_branches () in
                     loop br vs ((L.Tau, state_id)::ts) trans_list'
                   else
                     let state_id = spin_wait br2.state_id (-1) in
                     loop br vs ((Tau, state_id)::ts) trans_list'
                | Event (event, target) ->
                   let (b_new, target2, br2) = HT.add ht target br in
                   if b_new then
                     let state_id = Atomic.fetch_and_add next_state_id 1 in
                     Atomic.set br.state_id state_id;
                     Parstep.put xc (target, (Vis event, target2)::path, br);
                     let br = make_branches () in
                     loop br ((event, state_id)::vs) ts trans_list'
                   else
                     let state_id = spin_wait br2.state_id (-1) in
                     loop br ((event, state_id)::vs) ts trans_list'
                | Hidden (event, target) ->
                   let (b_new, target2, br2) = HT.add ht target br in
                   if b_new then
                     let state_id = Atomic.fetch_and_add next_state_id 1 in
                     Atomic.set br.state_id state_id;
                     Parstep.put xc (target, (Internal (Hid event), target2)::path, br);
                     let br = make_branches () in
                     loop br vs ((Hid event, state_id)::ts) trans_list'
                   else
                     let state_id = spin_wait br2.state_id (-1) in
                     loop br vs ((Hid event, state_id)::ts) trans_list'
                | Receive (ch, guard, targetf) ->
                   let (br, vs, ts) = collect_receive_transitions path br vs ts ch guard targetf in
                   loop br vs ts trans_list')
          in
          loop br [] [] trans_list
        in

        let rec loop br =
          match Parstep.get xc with
            None -> ()
          | Some (state, path, branches) ->
             let trans_list = transf state in
             if trans_list = [] then
               begin
                 Parstep.abort xc;
                 let _ = Atomic.compare_and_set deadlock_path None (Some path) in
                 Printf.printf "%d deadlock found\n" xc.id
               end
             else
               let (br, vs, ts) = collect_transitions path br trans_list in
               branches.vis_transitions <- vs;
               branches.tau_transitions <- ts;
               loop br

        in
        loop (make_branches ())
      in

      let ht = HT.create ht_size in
      let br = make_branches () in
      Atomic.set br.state_id 0;
      let _ = HT.add ht s0 br in
      Parstep.parstep ~b_progress num_workers chunk_size (s0, [(L.Internal Tau, s0)], br)
        (do_work ht transf);
      Printf.printf "max_chain_length: %d\n" (HT.max_chain_length ht);
      Printf.printf "conflicts: %d\n" (Atomic.get ht.c);
      Atomic.get deadlock_path

    let ht_to_vec1 ht s0 =
      let n = HT1.length ht in
      let vs = Array.make n s0 in
      let vv = Array.make n [] in
      let vt = Array.make n [] in
      HT1.iter
        (fun state (br : branches1) ->
          let i = br.state_id in
          vs.(i) <- state;
          vv.(i) <- br.vis_transitions;
          vt.(i) <- br.tau_transitions)
        ht;
      (vs, vv, vt)

    let ht_to_vec ht s0 =
      let n = Atomic.get ht.HT.n in
      let vs = Array.make n s0 in
      let vv = Array.make n [] in
      let vt = Array.make n [] in
      HT.iter
        (fun state br ->
          let i = Atomic.get br.state_id in
          vs.(i) <- state;
          vv.(i) <- br.vis_transitions;
          vt.(i) <- br.tau_transitions)
        ht;
      (vs, vv, vt)
    
    let ht_to_vec_par num_workers ht s0 =
      let n = Atomic.get ht.HT.n in
      let vs = Array.make n s0 in
      let vv = Array.make n [] in
      let vt = Array.make n [] in
      HT.par_iter num_workers
        (fun state br ->
          let i = Atomic.get br.state_id in
          if not (0 <= i && i < n) then
            (Printf.printf "%d %d\n" i n; flush stdout);
          assert (0 <= i && i < n);
          assert (vs.(i) == s0);
          vs.(i) <- state;
          vv.(i) <- br.vis_transitions;
          vt.(i) <- br.tau_transitions)
        ht;
      (vs, vv, vt)

end
