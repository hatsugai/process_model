open Printf
open Type

module type ProcessModel =
  sig
    type event
    type channel
    val show_event : event -> string
    val show_channel : channel -> string

    type trans =
      Event of event * process
    | Receive of channel * (event -> bool) * (event -> process)

    and tau_trans = event TransitionLabel.ievent * process

    and anatomy =
      Alone
    | Choice of process list
    | InternalChoice of process list
    | ConcurrentComposition of process list
    | Interleave of process list
    | SequentialComposition of process * process
    | Hide of process
    | Rename of process

    and transf_res =  trans list * tau_trans list

    and process =
      < transitions : transf_res;
      tick : bool;
      class_id : int;
      compare : process -> int;
      equal : process -> bool;
      set_state : unit;
      hash : int;
      anatomy : anatomy;
      pwalk : unit;
      show : string >

    val transitions : process -> transf_res
    val equal_process : process -> process -> bool
    val compare_process : process -> process -> int
    val hash_process : process -> int
    val show_process : process -> string
    val anatomy : process -> anatomy
    val pwalk : process -> unit

    type 'state process_class = {
        transf : ('state -> process) -> 'state -> transf_res;
        compare : 'state -> 'state -> int;
        hash : 'state -> int;
        show : 'state -> string;
        pwalk : 'state -> unit;
        mutable state : 'state;
      }

    val make_process_class :
      (('s -> process) -> 's -> trans list) ->
      ('s -> 's -> int) ->
      ('s -> int) -> ('s -> string) -> ?pwalk:('s -> unit) -> 's -> 's process_class
    val make_process_class_tau :
      (('s -> process) -> 's -> trans list * tau_trans list) ->
      ('s -> 's -> int) ->
      ('s -> int) -> ('s -> string) -> ?pwalk:('s -> unit) -> 's -> 's process_class
    val make_process : 's process_class -> 's -> process

    val omega : process
    val stop : process
    val skip : process

    val choice : process list -> process
    val internal_choice : ?pwalk:(unit -> unit) -> process list -> process
    val composition : (event -> channel) -> (channel -> bool) -> process list -> process
    val interleave : process list -> process
    val hide : (event -> channel) -> (channel -> bool) -> process -> process
    val sequential_composition : process -> process -> process
    val guard_true : event -> bool
  end

module Make (E : EventType) (C : ChannelType) : ProcessModel
       with type event = E.t
       with type channel = C.t
  =
  struct
    type event = E.t
    type channel = C.t
    let show_event  = E.show
    let show_channel  = C.show

    let guard_true _ = true

    type trans =
      Event of event * process
    | Receive of channel * (event -> bool) * (event -> process)

    and tau_trans = event TransitionLabel.ievent * process

    and anatomy =
      Alone
    | Choice of process list
    | InternalChoice of process list
    | ConcurrentComposition of process list
    | Interleave of process list
    | SequentialComposition of process * process
    | Hide of process
    | Rename of process
    
    and transf_res =  trans list * tau_trans list

    and process =
      < transitions : transf_res;
      tick : bool;
      class_id : int;
      compare : process -> int;
      equal : process -> bool;
      set_state : unit;
      hash : int;
      anatomy : anatomy;
      pwalk : unit;
      show : string >

    class virtual process_abstract =
      object (self)
        method virtual transitions : transf_res
        method virtual tick : bool
        method virtual class_id : int
        method virtual compare : process_abstract -> int
        method virtual set_state : unit
        method virtual hash : int
        method virtual anatomy : anatomy
        method virtual pwalk : unit
        method virtual show : string
        method equal p = self#compare p = 0
      end

    let transitions p = p#transitions
    let equal_process p q = p#equal q
    let compare_process p q = p#compare q
    let hash_process p = p#hash
    let show_process p = p#show
    let anatomy p = p#anatomy
    let pwalk p = p#pwalk

    type 'state process_class = {
        transf : ('state -> process) -> 'state -> transf_res;
        compare : 'state -> 'state -> int;
        hash : 'state -> int;
        show : 'state -> string;
        pwalk : 'state -> unit;
        mutable state : 'state;
      }

    let obj_adr x : int = Obj.obj (Obj.repr x)

    class process_concrete process_class initial_state =
      object (self)
        inherit process_abstract
        val state = initial_state
        method transitions =
          let pk state = (({<state>}) :> process) in
          process_class.transf pk state
        method tick = false
        method compare p =
          let s = self#class_id - p#class_id in
          if s <> 0 then
            s
          else
            (p#set_state;
             process_class.compare state process_class.state)
        method class_id = obj_adr process_class
        method set_state = process_class.state <- state
        method hash = process_class.hash state
        method anatomy = Alone
        method pwalk = process_class.pwalk state
        method show = process_class.show state
      end

    let make_process_class transf compare hash show
          ?(pwalk=(fun _ -> ())) state =
      let transf pk state = (transf pk state, []) in
      { transf; compare; hash; show; pwalk; state }

    let make_process_class_tau transf compare hash show
          ?(pwalk=(fun _ -> ())) state =
      { transf; compare; hash; show; pwalk; state }

    let make_process process_class initial_state =
      ((new process_concrete process_class initial_state) :> process)

    module SyncTerm =
      struct
        type t =
          Send of E.t * process
        | Recv of (event -> bool) * (event -> process)
      end

    let omega_ref = ref 0

    let omega =
      object (self)
        inherit process_abstract
        method transitions = ([], [])
        method tick = false
        method class_id = obj_adr omega_ref
        method compare p = if self#class_id = p#class_id then 0 else (-1)
        method set_state = ()
        method hash = 0
        method anatomy = Alone
        method pwalk = ()
        method show = "OMEGA"
      end

    let stop_ref = ref 0

    let stop =
      object (self)
        inherit process_abstract
        method transitions = ([], [])
        method tick = false
        method class_id = obj_adr stop_ref
        method compare p = if self#class_id = p#class_id then 0 else (-1)
        method set_state = ()
        method hash = 0
        method anatomy = Alone
        method pwalk = ()
        method show = "STOP"
      end

    let skip_ref = ref 0

    let skip =
      object (self)
        inherit process_abstract
        method transitions = ([], [])
        method tick = true
        method class_id = obj_adr skip_ref
        method compare p = if self#class_id = p#class_id then 0 else (-1)
        method set_state = ()
        method hash = 0
        method anatomy = Alone
        method pwalk = ()
        method show = "SKIP"
      end

    (*** internal choice **********************************************)

    let compare_process_list ps qs =
      let rec loop ps qs =
        match ps, qs with
          [], [] -> 0
        | p::ps', q::qs' ->
           let s = compare_process p q in
           if s <> 0 then
             s
           else
             loop ps' qs'
        | _, _ -> Error.f __FUNCTION__
      in
      loop ps qs

    let show_process_list ps =
      let s =
        match ps with
          [] -> ""
        | p::ps' ->
           List.fold_left
             (fun s p -> sprintf "%s; %s" s (p#show))
             (p#show) ps'
      in
      "[" ^ s ^ "]"

    class process_internal_choice (pwalk : unit -> unit) (ps : process list) =
      let ref_ps = ref ps in
      object (self)
        inherit process_abstract
        val ps = ps
        method transitions = ([], List.map (fun p -> (TransitionLabel.Tau, p)) ps)
        method tick = false
        method class_id = obj_adr ps
        method compare p =
          let s = self#class_id - p#class_id in
          if s <> 0 then
            s
          else
            (p#set_state;
             compare_process_list ps !ref_ps)
        method set_state = ref_ps := ps
        method hash =
          List.fold_left (fun hv p -> hv + hash_process p) 0 ps
        method anatomy = InternalChoice ps
        method pwalk = pwalk ()
        method show = "|~|" ^ (show_process_list ps)
      end

    let internal_choice ?(pwalk = fun () -> ()) ps =
      match ps with
        [] -> Error.f __FUNCTION__
      | [_] -> Error.f __FUNCTION__
      | _ -> ((new process_internal_choice pwalk ps) :> process)

    (*** external choice **********************************************)

    let external_choice pk ps =
      let rec loop vis_ts tau_ts rs i ps =
        match ps with
          [] -> (vis_ts, tau_ts)
        | p::ps' ->
           let (vs, ts) = transitions p in
           let ts =
             List.map
               (fun (htag, q) ->
                 (htag, pk (List.rev_append rs (q::ps'))))
               ts
           in
           loop (vs @ vis_ts) (ts @ tau_ts) (p::rs) (i+1) ps'
      in
      loop [] [] [] 0 ps

    class process_external_choice (ps : process list) =
      let ref_ps = ref ps in
      object (self)
        inherit process_abstract
        val ps = ps
        method transitions =
          let pk ps = ({<ps>} :> process) in
          external_choice pk ps
        method tick = List.exists (fun p -> p#tick) ps
        method class_id = obj_adr ps
        method compare p =
          let s = self#class_id - p#class_id in
          if s <> 0 then
            s
          else
            (p#set_state;
             compare_process_list ps !ref_ps)
        method set_state = ref_ps := ps
        method hash =
          List.fold_left (fun hv p -> hv + hash_process p) 0 ps
        method anatomy = Choice ps
        method pwalk = ()
        method show = "[]" ^ (show_process_list ps)
      end

    let choice ps =
      match ps with
        [] -> Error.f __FUNCTION__
      | [p] -> p
      | _ -> ((new process_external_choice ps) :> process)

    (*** concurrent composition ***************************************)

    module CHT = Hashtbl.Make (C)

    let composition_imp event_to_channel sync pk ps =
      let n = List.length ps in
      let ht = CHT.create 0 in
      let reg ch i term =
        let v =
          match CHT.find_opt ht ch with
            None ->
             let v = Array.make n [] in
             CHT.add ht ch v;
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
             Some (Event (e, pk qs))
          | y::ys' ->
             (match y with
                SyncTerm.Send (e', q) ->
                 if E.equal e e' then
                   loop_ev e (q::rs) ys'
                 else
                   None
              | Recv (g, tf) ->
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
                              pk qs)))
          | y::ys' ->
             (match y with
                SyncTerm.Send (e, q) ->
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
            | SyncTerm.Send (e, q) -> loop_ev e [q] ys'
            | Recv (g, tf) -> loop_recv [g] [tf] ys')
      in

      let sync_trans vists tauts =
        let vists =
          CHT.fold
            (fun ch v acc ->
              let xss = Array.to_list v in
              let yss = Util.cartesian_product xss in
              List.fold_left
                (fun acc ys ->
                  match consensus ch ys with
                    None -> acc
                  | Some t -> t::acc)
                acc yss)
            ht vists
        in
        (vists, tauts)
      in

      let rec loop vists tauts i rs ps =
        match ps with
          [] -> sync_trans vists tauts
        | p::ps' ->
           let (xs, ts) = transitions p in
           let rec scan vists xs =
             match xs with
               [] ->
                let tauts =
                  List.fold_left
                    (fun tauts (htag, q) ->
                      (htag, pk (List.rev_append rs (q::ps')))::tauts)
                    tauts ts
                in
                let tauts =
                  if p#tick then
                    (TransitionLabel.ITick, pk (List.rev_append rs (omega::ps')))::tauts
                  else tauts
                in
                loop vists tauts (i+1) (p::rs) ps'
             | x::xs' ->
                (match x with 
                   Event (e, p') ->
                    let ch = event_to_channel e in
                    if sync ch then
                      (reg ch i (Send (e, p')); scan vists xs')
                    else
                      let q = pk (List.rev_append rs (p'::ps')) in
                      scan (Event (e, q)::vists) xs'
                 | Receive (ch, guard, targetf) ->
                    if sync ch then
                      (reg ch i (SyncTerm.Recv (guard, targetf));
                       scan vists xs')
                    else
                      let x_targetf e =
                        pk (List.rev_append rs (targetf e::ps'))
                      in
                      scan (Receive (ch, guard, x_targetf)::vists) xs')
           in
           scan vists xs
      in
      loop [] [] 0 [] ps

    class process_composition event_to_channel sync (ps : process list) =
      let ref_ps = ref ps in
      object (self)
        inherit process_abstract
        val ps = ps
        method transitions =
          let pk ps = (({<ps>}) :> process) in
          composition_imp event_to_channel sync pk ps
        method tick =
          List.for_all (fun p -> p#equal omega) ps
        method class_id = obj_adr ref_ps
        method compare p =
          let s = self#class_id - p#class_id in
          if s <> 0 then
            s
          else
            (p#set_state; compare_process_list ps !ref_ps)
        method set_state = ref_ps := ps
        method hash =
          List.fold_left (fun hv p -> hv + hash_process p) 0 ps
        method anatomy = ConcurrentComposition ps
        method pwalk =
          List.iter (fun p -> p#pwalk) ps
        method show = "||" ^ (show_process_list ps)
      end

    let composition event_to_channel sync ps =
      ((new process_composition event_to_channel sync ps) :> process)

    let single xs =
      match xs with
        [_] -> true
      | _ -> false

    let interleave_imp pk ps =
      let rec loop vists tauts i rs ps =
        match ps with
          [] -> (vists, tauts)
        | p::ps' ->
           let (xs, ts) = transitions p in
           let rec scan vists xs =
             match xs with
               [] ->
                let tauts =
                  List.fold_left
                    (fun tauts (htag, q) ->
                      (htag, pk (List.rev_append rs (q::ps')))::tauts)
                    tauts ts
                in
                let tauts =
                  if p#tick then
                    (if rs=[] && ps'=[] then
                       Error.f "interleave: cannot happen"
                     else if single rs && ps'=[] then
                       (TransitionLabel.ITick, List.hd rs)::tauts
                     else if single ps' && rs=[] then
                       (ITick, List.hd ps')::tauts
                     else
                       (ITick, pk (List.rev_append rs ps'))::tauts)
                  else tauts
                in
                loop vists tauts (i+1) (p::rs) ps'

             | x::xs' ->
                (match x with 
                   Event (e, p') ->
                    let s' = pk (List.rev_append rs (p'::ps')) in
                    scan (Event (e, s')::vists) xs'
                 | Receive (ch, guard, targetf) ->
                    let x_targetf e =
                      pk (List.rev_append rs (targetf e::ps'))
                    in
                    scan (Receive (ch, guard, x_targetf)::vists) xs')
           in
           scan vists xs
      in
      loop [] [] 0 [] ps

    class process_interleave (ps : process list) =
      let ref_ps = ref ps in
      object (self)
        inherit process_abstract
        val ps = ps
        method transitions =
          let pk ps = (({<ps>}) :> process) in
          interleave_imp pk ps
        method tick = false
        method class_id = obj_adr ref_ps
        method compare p =
          let s = self#class_id - p#class_id in
          if s <> 0 then
            s
          else
            (p#set_state; compare_process_list ps !ref_ps)
        method set_state = ref_ps := ps
        method hash =
          List.fold_left (fun hv p -> hv + hash_process p) 0 ps
        method anatomy = Interleave ps
        method pwalk =
          List.iter (fun p -> p#pwalk) ps
        method show = "|||" ^ (show_process_list ps)
      end

    let interleave ps =
      match ps with
        [] -> Error.f __FUNCTION__
      | [p] -> p
      | _ -> ((new process_interleave ps) :> process)

    (*** hide *********************************************************)

    module EHT = Hashtbl.Make(E)

    class process_hide event_to_channel ch_pred p0 =
      let ref_p = ref p0 in
      object (self)
        inherit process_abstract
        val process = p0
        method transitions =
          let pk p = (({<process=p>}) :> process) in
          let (vists, tauts) = transitions process in
          let rec loop vists tauts xs =
            match xs with
              [] -> (vists, tauts)
            | x::xs' ->
               (match x with
                  Event (e, p') ->
                   let ch = event_to_channel e in
                   if ch_pred ch then
                     loop vists ((TransitionLabel.Hid e, pk p')::tauts) xs'
                   else
                     loop (Event (e, pk p')::vists) tauts xs'
                | Receive (ch, g, f) ->
                   if ch_pred ch then
                     Error.f "tried to hide receive"
                   else
                     let t = Receive (ch, g, (fun e -> pk (f e))) in
                     loop (t::vists) tauts xs')
          in
          let tauts = List.map (fun (htag, p) -> (htag, pk p)) tauts in
          loop [] tauts vists
        method tick = process#tick
        method class_id = obj_adr ref_p
        method compare p =
          assert (self#class_id = p#class_id);
          p#set_state;
          process#compare !ref_p
        method set_state = ref_p := process
        method hash = process#hash * 2 + 1
        method anatomy = Hide process
        method pwalk = process#pwalk
        method show = "hide(" ^ process#show ^ ")"
      end

    let hide event_to_channel ch_pred process =
      ((new process_hide event_to_channel ch_pred process) :> process)

    (*** sequential composition ***************************************)

    class process_seq p0 q =
      let ref_p = ref p0 in
      object (self)
        inherit process_abstract
        val process = p0
        method transitions =
          let pk p = (({<process=p>}) :> process) in
          let (vists, tauts) = transitions process in
          let vists =
            List.map
              (fun t ->
                match t with
                  Event (e, p') -> Event (e, pk p')
                | Receive (ch, guard, targetf) ->
                   Receive (ch, guard, fun e -> pk (targetf e)))
              vists
          in
          let tauts = List.map (fun (htag, q) -> (htag, pk q)) tauts in
          let tauts = if process#tick then (TransitionLabel.ITick, q)::tauts else tauts in
          (vists, tauts)
        method tick = false
        method class_id = obj_adr ref_p
        method compare p =
          let s = self#class_id - p#class_id in
          if s <> 0 then
            s
          else
            (p#set_state; process#compare !ref_p)
        method set_state = ref_p := process
        method hash = process#hash
        method anatomy = SequentialComposition (process, q)
        method pwalk = process#pwalk
        method show = "(" ^ process#show ^ "; " ^ q#show ^ ")"
      end

    let sequential_composition p q =
      ((new process_seq p q) :> process)

  end
