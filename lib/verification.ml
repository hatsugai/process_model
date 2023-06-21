open Printf
open Process

module type Verification =
  sig
    type event
    type channel
    type ievent
    type process

    module A : sig
      type t = Tau | Tick | Event of event | Hid of event | ITick
      val pp : Format.formatter -> t -> unit
      val show : t -> string
      val equal : t -> t -> bool
      val compare : t -> t -> int
    end

    module V : sig
      type t = Tick | Event of event
      val pp : Format.formatter -> t -> unit
      val show : t -> string
      val equal : t -> t -> bool
      val compare : t -> t -> int
    end

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

    module IntSet : Set.S
    module ES : Set.S
    module ESS : Set.S

    type check_traces_result =
        CT_Violation of ((int * int) * A.t) list
      | CT_Ok

    type check_failures_result =
        CF_TraceViolation of ((int * int) * A.t) list
      | CF_RefusalViolation of ESS.t * ES.t * int * int *
          ((int * int) * A.t) list
      | CF_Ok

    val unfold : (channel -> event list) -> process -> process ltsx
    val det : lts -> IntSet.t ltsx
    val check_traces : lts -> lts -> check_traces_result
    val min_acceptances : lts -> IntSet.t ltsx -> ESS.t array
    val check_failures : lts -> ESS.t array -> lts -> check_failures_result

    val print_trace_violation :
      IntSet.t ltsx -> 'a ltsx -> 'b ltsx ->
      int * ((int * int) * A.t) list ->
      unit

    val print_refusals_violation :
      IntSet.t ltsx ->
      'a ltsx ->
      'b ltsx -> ESS.t -> ES.t -> int -> int -> ((int * int) * A.t) list -> unit

  end

module Make (P : ProcessModel) : Verification
       with type event = P.event
       with type channel = P.channel
       with type ievent = P.H.t
       with type process = P.process
  =
  struct
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

    (*** determinize **************************************************)

    module IntSet =
      Set.Make (
          struct
            type t = int
            let compare = compare
          end)

    module SSHT =
      Hashtbl.Make(
          struct
            type t = IntSet.t
            let equal = IntSet.equal
            let hash s = IntSet.fold (fun x a -> a + x) s 0
          end)

    module EHT =
      Hashtbl.Make (
          struct
            type t = P.event
            let equal = P.equal_event
            let hash e = P.hash_event e
          end)

    let tau_closure tau_transv ss =
      let que = Queue.create () in
      let x = ref ss in
      IntSet.iter (fun s -> Queue.add s que) ss;
      while not (Queue.is_empty que) do
        let s = Queue.take que in
        let ts = tau_transv.(s) in
        List.iter
          (fun (_, q) ->
            if not (IntSet.mem q !x) then
              (Queue.add q que; x := IntSet.add q !x))
          ts;
      done;
      !x

    let ht_update ht e t =
      match EHT.find_opt ht e with
        None ->
         EHT.add ht e (IntSet.singleton t)
      | Some ss ->
         EHT.replace ht e (IntSet.add t ss)

    let det lts =
      let ht = SSHT.create 0 in
      let que = Queue.create () in
      let add s =
        match SSHT.find_opt ht s with
          None ->
           let id = SSHT.length ht in
           let r = ref ([], [], false) in
           SSHT.replace ht s (id, r);
           Queue.add (s, r) que;
           id
        | Some (id, _) -> id
      in
      let ss0 = tau_closure lts.tau_transv (IntSet.singleton 0) in
      let _ = add ss0 in
      while not (Queue.is_empty que) do
        let (ss, r) = Queue.take que in
        (* ss からの遷移を求める *)
        let r_tick = ref false in
        let trans =
          let ht = EHT.create 0 in
          IntSet.iter
            (fun s ->
              (if lts.tickv.(s) then r_tick := true);
              List.iter
                (fun (e, t) -> ht_update ht e t)
                lts.vis_transv.(s))
            ss;
          EHT.fold
            (fun e tt trans ->
              let tc = tau_closure lts.tau_transv tt in
              let id = add tc in
              (e, id)::trans)   (* target はここで id に変換してしまう *)
            ht []
        in
        r := (trans, [], !r_tick)
      done;
      (* translate ht to lts *)
      let (lts, statev) =
        ht_to_vec SSHT.length SSHT.iter ss0 ht
      in
      let show s =
        let str =
          IntSet.fold
            (fun id str -> sprintf "%s %d" str id)
            statev.(s) "{"
        in str ^ " }"
      in
      { lts; statev; show }

    (*** traces *******************************************************)

    module IntPair =
      struct
        type t = int * int
        let equal (p1, q1) (p2, q2) = p1 = p2 && q1 = q2
        let hash (p, q) = p * 17 + q
      end

    module HT_IntPair = Hashtbl.Make (IntPair)

    type check_traces_result =
      CT_Violation of ((int * int) * A.t) list
    | CT_Ok

    (* version: transitions are not recorded in ht *)
    let check_traces ltsp ltsq =
      let ht = HT_IntPair.create 0 in
      let que = Queue.create () in
      let add x path =
        if not (HT_IntPair.mem ht x) then
          (HT_IntPair.replace ht x true;
           Queue.add (x, path) que)
      in
      let rec loop () =
        if Queue.is_empty que then
          CT_Ok
        else
          let ((p, q), path) = Queue.take que in
          (* sliding by tau trans *)
          List.iter
            (fun (htag, q') ->
              let atag = htag_to_atag htag in
              add (p, q') (((p, q), atag)::path))
            ltsq.tau_transv.(q);
          (* inclusion of trans *)
          let p_trans = ltsp.vis_transv.(p) in
          let rec scan eqs =
            match eqs with
              [] ->
               (* check tick *)
               if ltsq.tickv.(q) && not ltsp.tickv.(p) then
                 CT_Violation (((p, q), A.Tick)::path)
               else
                 loop ()
            | (e, q')::eqs' ->
               match List.assoc_opt e p_trans with
                 None -> CT_Violation (((p, q), A.Event e)::path)
               | Some p' ->
                  add (p', q') (((p, q), A.Event e)::path);
                  scan eqs'
          in
          scan ltsq.vis_transv.(q);
      in
      add (0, 0) [];
      loop ()

    let print_ss dlts lts s =
      let ss = dlts.statev.(s) in
      IntSet.iter
        (fun s -> printf "  %s\n" (lts.show s))
        ss

    let print_path dlts_spec lts_spec lts_imp path =
      List.iteri
        (fun i ((p, q), event) ->
          printf "--- %d -------------------------------------\n" i;
          printf "SPEC\n";
          print_ss dlts_spec lts_spec p;
          printf "IMP\n";
          printf "  %s\n" (lts_imp.show q);
          printf "-----------------------------------------\n";
          printf "EVENT %s\n" (A.show event))
        path

    let print_trace_violation dlts_spec lts_spec lts_imp (q, path) =
      printf "trace violation\n";
      print_path dlts_spec lts_spec lts_imp (List.rev path);
      printf "-----------------------------------------\n";
      printf "IMP\n";
      printf "  %s\n" (lts_imp.show q)

    (*** stable failures **********************************************)

    module ES =
      struct
        include
          Set.Make (
              struct
                type t = V.t
                let compare = V.compare
              end)
        let show s =
          let acc =
            fold
              (fun e acc ->
                if acc = "" then V.show e else
                  sprintf "%s %s" acc (V.show e))
              s ""
          in
          "{" ^ acc ^ "}"
      end

    module ESS =
      struct
        include
          Set.Make (
              struct
                type t = ES.t
                let compare = ES.compare
              end)
        let show ss =
          let acc =
            fold
              (fun s acc ->
                if acc="" then ES.show s
                else sprintf "%s %s" acc (ES.show s))
              ss ""
          in
          acc
      end

    let stable_state_initials ltsq q =
      List.fold_left
        (fun s (e, _) -> ES.add (V.Event e) s)
        (if ltsq.tickv.(q) then ES.singleton V.Tick else ES.empty)
        ltsq.vis_transv.(q)

    let minaccs_of_ss lts ss =
      IntSet.fold
        (fun s acc ->
          if lts.tau_transv.(s) = [] then
            let initials = stable_state_initials lts s in
            ESS.add initials acc
          else                  (* unstable *)
            acc)
        ss ESS.empty

    let min_acceptances lts dlts =
      let n = Array.length dlts.statev in
      let vaccs = Array.make n ESS.empty in
      for i = 0 to n - 1 do
        vaccs.(i) <- minaccs_of_ss lts dlts.statev.(i)
      done;
      vaccs

    let check_refusals spec_acceptances ltsq q =
      if ltsq.tau_transv.(q) = [] then
        let initials = stable_state_initials ltsq q in
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
      CF_TraceViolation of ((int * int) * A.t) list
    | CF_RefusalViolation of ESS.t * ES.t * int * int * ((int * int) * A.t) list
    | CF_Ok
    
    let check_failures ltsp vaccs ltsq =
      let ht = HT_IntPair.create 0 in
      let que = Queue.create () in
      let add x path =
        if not (HT_IntPair.mem ht x) then
          (HT_IntPair.replace ht x true;
           Queue.add (x, path) que)
      in
      let rec loop () =
        if Queue.is_empty que then
          CF_Ok
        else
          let ((p, q), path) = Queue.take que in
          (* check refusals *)
          match check_refusals vaccs.(p) ltsq q with
            Some initials ->
             CF_RefusalViolation (vaccs.(p), initials, p, q, path)
          | None ->
             (* sliding by tau trans *)
             List.iter
               (fun (htag, q') ->
                 let atag = htag_to_atag htag in
                 add (p, q') (((p, q), atag)::path))
               ltsq.tau_transv.(q);
             (* inclusion of trans *)
             let p_trans = ltsp.vis_transv.(p) in
             let rec scan eqs =
               match eqs with
                 [] ->
                  (* check tick *)
                  if ltsq.tickv.(q) && not ltsp.tickv.(p) then
                    CF_TraceViolation (((p, q), A.Tick)::path)
                  else
                    loop ()
               | (e, q')::eqs' ->
                  match List.assoc_opt e p_trans with
                    None -> CF_TraceViolation (((p, q), A.Event e)::path)
                  | Some p' ->
                     add (p', q') (((p, q), A.Event e)::path);
                     scan eqs'
             in
             scan ltsq.vis_transv.(q);
      in
      add (0, 0) [];
      loop ()

    let print_refusals_violation dlts_spec lts_spec lts_imp
          minaccs initials p q path =
      print_path dlts_spec lts_spec lts_imp (List.rev path);
      printf "----------------------------------------\n";
      printf "SPEC\n";
      print_ss dlts_spec lts_spec p;
      printf "IMP\n";
      printf "  %s\n" (lts_imp.show q);
      printf "----------------------------------------\n";
      printf "SPEC initials set: %s\n" (ESS.show minaccs);
      printf "IMP initials: %s\n" (ES.show initials)

  end
