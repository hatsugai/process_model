open Printf
open Type
open Transf

module Make (E : EventType) (C : ChannelType) (S : StateType) =
  struct

    module L = TransitionLabel

    type command = Index of int | Undo | History

    let print_transitions ts =
      List.iteri
        (fun i t ->
          printf "%d. " i;
          match t with
            Tau p -> printf "T %s\n" (S.show p)
          | Event (e, p) ->
             printf "E %s %s\n" (E.show e) (S.show p)
          | Hidden (e, p) ->
             printf "H %s %s\n" (E.show e) (S.show p)
          | Receive (ch, _g, _f) ->
             printf "R %s\n" (C.show ch))
        ts

    let rec input () =
      let x = read_line () in
      if x <> "" && x.[0] = 'u' then
        Undo
      else if x <> "" && x.[0] = 'h' then
        History
      else
        try
          Scanf.sscanf x "%d" (fun k -> Index k)
        with
          _ ->
          printf "error |%s|\n" x;
          input ()

    let print_receive_trans show_event _targetf es =
      List.iteri
        (fun i e ->
          printf "  %d. %s\n" i (show_event e))
        es

    let print_history hist =
      List.iteri
        (fun i (u, s) ->
          printf "%d. %s %s\n" i (L.show_revent E.show u) (S.show s))
        hist

    let simulation channel_to_event_list transf p =

      let rec loop hist (p : S.t) =
        let ts = transf p in
        let ts =
          List.filter
            (fun syncterm ->
              match syncterm with
                Receive (ch, guard, _) ->
                 List.exists guard (channel_to_event_list ch)  
              | _ -> true)
            ts
        in
        let n = List.length ts in
        let rec command () =
          printf "> "; flush stdout;
          match input () with
            Undo ->
             (match hist with
                [] -> printf "no history\n"; command ()
              | (_, p)::hist' -> loop hist' p)
          | History ->
             print_history hist;
             loop hist p
          | Index k ->
             if k >= 0 && k < n then
               (match List.nth ts k with
                  Tau q -> loop ((L.Internal Tau, p)::hist) q
                | Event (e, q) -> loop ((L.Vis e, p)::hist) q
                | Hidden (e, q) -> loop ((L.Internal (Hid e), p)::hist) q
                | Receive (ch, g, f) ->
                   let es = List.filter g (channel_to_event_list ch) in
                   let m = List.length es in
                   print_receive_trans E.show f es;
                   let rec sel_arg () =
                     printf ">> "; flush stdout;
                     match input () with
                       Undo -> command ()
                     | History -> command ()
                     | Index i ->
                        if i >= 0 && i < m then
                          let e = List.nth es i in
                          let q = f e in
                          loop ((Vis e, p)::hist) q
                        else
                          sel_arg ()
                   in
                   sel_arg ())
             else
               (command ())
        in
        printf "========================================\n";
        printf "%s\n" (S.show p);
        print_transitions ts;
        command ()
      in
      loop [] p
end
