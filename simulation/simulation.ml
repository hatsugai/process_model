open Printf
open Process_model

module type Simulation =
  sig
    type event
    type channel
    type process
    val simulation : (channel -> event list) -> process -> unit
  end

module Make(P : ProcessModel) : Simulation
       with type event = P.event
       with type channel = P.channel
       with type process = P.process
  =
  struct
    type event = P.event
    type channel = P.channel
    type process = P.process

    type command = Index of int | Undo

    let show_trans t =
      match t with
        P.Event (e, p) ->
         sprintf "%s -> %s" (P.show_event e) (P.show_process p)
      | Receive (ch, _g, _f) -> P.show_channel ch

    let print_transitions vs ts tick =
      let m = List.length vs in
      let n = List.length ts in
      List.iteri
        (fun i t -> printf "%d. %s\n" i (show_trans t))
        vs;
      List.iteri
        (fun i (htag, q) ->
          printf "%d. %s -> %s\n" (m+i) (P.H.show htag) (P.show_process q))
        ts;
      (if tick then
         printf "%d. tick -> OMEGA\n" (m+n))

    let rec input () =
      let x = read_line () in
      if x <> "" && x.[0] = 'u' then
        Undo
      else
        try
          Scanf.sscanf x "%d" (fun k -> Index k)
        with
          _ ->
          printf "error |%s|\n" x;
          input ()

    let print_receive_trans show_event targetf es =
      List.iteri
        (fun i e ->
          let p = targetf e in
          printf "  %d. %s -> %s\n" i (show_event e) (P.show_process p))
        es

    let simulation channel_to_event_list p =

      let rec loop (hist : P.process list) (p : P.process) =
        let (vs, ts) = P.transitions p in
        let m = List.length vs in
        let n = List.length ts in
        let rec command () =
          printf "> "; flush stdout;
          match input () with
            Undo ->
             (match hist with
                [] -> printf "no history\n"; command ()
              | p::hist' -> loop hist' p)
          | Index k ->
             if k >= 0 && k < m then
               (match List.nth vs k with
                  Event (_e, q) -> loop (p::hist) q
                | Receive (ch, g, f) ->
                   let es = List.filter g (channel_to_event_list ch) in
                   let m = List.length es in
                   print_receive_trans P.show_event f es;
                   let rec sel_arg () =
                     printf ">> "; flush stdout;
                     match input () with
                       Undo -> command ()
                     | Index i ->
                        if i >= 0 && i < m then
                          let e = List.nth es i in
                          let q = f e in
                          loop (p::hist) q
                        else
                          sel_arg ()
                   in
                   sel_arg ())
             else if k >= m && k < m+n then
               let (_htag, q) = List.nth ts (k-m) in
               loop (p::hist) q
             else if k=m+n && p#tick then
               loop (p::hist) P.omega
             else
               (command ())
        in
        printf "%s\n" (P.show_process p);
        print_transitions vs ts p#tick;
        command ()
      in
      loop [] p
  end
