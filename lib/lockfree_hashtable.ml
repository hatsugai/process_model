exception Error
exception CannotHappen

module type HashedType =
  sig
    type t
    val equal: t -> t -> bool
    val hash: t -> int
  end

module Make(H: HashedType) =
  struct
    type 'a node =
      Nil
    | Cons of H.t * 'a * 'a node Atomic.t

    type 'a t = {
        v : 'a node Atomic.t array;
        c : int Atomic.t;
        n : int Atomic.t;
      }

    let length ht = Atomic.get ht.n
    let conflict_count ht = Atomic.get ht.c

    let iter f ht =
      let rec scan p =
        match Atomic.get p with
          Nil -> ()
        | Cons (key, data, next) ->
           f key data; scan next
      in
      let n = Array.length ht.v in
      for i=0 to n-1 do
        scan ht.v.(i)
      done

    let par_iter num_workers f ht =
      let rec scan p =
        match Atomic.get p with
          Nil -> ()
        | Cons (key, data, next) ->
           f key data; scan next
      in
      let f start end_1 =
        for i = start to end_1 do
          scan ht.v.(i)
        done
      in
      Par_iter.par_iter num_workers (Array.length ht.v) f

    let fold f ht acc =
      let rec scan acc p =
        match Atomic.get p with
          Nil -> acc
        | Cons (key, data, next) ->
           scan (f key data acc) next
      in
      let n = Array.length ht.v in
      let rec loop acc i =
        if i=n then acc else loop (scan acc ht.v.(i)) (i+1)
      in
      loop acc 0

    let create n =
      let head0 = Atomic.make Nil in
      let v = Array.make n head0 in
      for i=0 to n-1 do v.(i) <- Atomic.make Nil done;
      { v; c = Atomic.make 0; n = Atomic.make 0 }

    let find ht key =
      let i = H.hash key mod Array.length ht.v in
      let rec scan p =
        match Atomic.get p with
          Nil -> raise Error
        | Cons (k, x, next) ->
           if H.equal k key then
             x
           else
             scan next
      in
      scan ht.v.(i)

    let find_opt ht key =
      let i = H.hash key mod Array.length ht.v in
      let rec scan p =
        match Atomic.get p with
          Nil -> None
        | Cons (k, x, next) ->
           if H.equal k key then
             Some x
           else
             scan next
      in
      scan ht.v.(i)

    let add ht key data =
      let link_cell = Atomic.make Nil in
      let p = Cons (key, data, link_cell) in
      let i = H.hash key mod Array.length ht.v in
      let rec loop tail =
        let head_cell = ht.v.(i) in
        let head = Atomic.get head_cell in
        let rec scan q =
          if q == tail then
            begin
              Atomic.set link_cell head;
              if Atomic.compare_and_set head_cell head p then
                (Atomic.incr ht.n; (true, key, data))
              else
                (Atomic.incr ht.c; Domain.cpu_relax (); loop head)
            end
          else
            match q with
              Nil -> raise CannotHappen
            | Cons (k, x, next) ->
               if H.equal k key then
                 (false, k, x)
               else
                 scan (Atomic.get next)
        in
        scan head
      in
      loop Nil

    let rec len c (a : 'a node Atomic.t) =
      match Atomic.get a with
        Nil -> c
      | Cons (_, _, a') -> len (c+1) a'

    let max_chain_length ht =
      Array.fold_left
        (fun max a ->
          let k = len 0 a in
          if max >= k then max else k)
        0 ht.v

  end
