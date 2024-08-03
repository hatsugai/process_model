exception CannotHappen

type 'a t = 'a list Atomic.t

let num_conflicts_push = Atomic.make 0
let num_conflicts_pop = Atomic.make 0

let make () = Atomic.make []

let rec push (stack : 'a list Atomic.t) (data : 'a) =
  let xs = Atomic.get stack in
  let xs' = data::xs in
  if Atomic.compare_and_set stack xs xs' then
    ()
  else
    begin
      Atomic.incr num_conflicts_push;
      push stack data
    end

let rec pop (stack : 'a Atomic.t) =
  let xs = Atomic.get stack in
  match xs with
    [] -> None
  | x::xs' ->
     if Atomic.compare_and_set stack xs xs' then
       Some x
     else
       begin
         Atomic.incr num_conflicts_pop;
         pop stack
       end
