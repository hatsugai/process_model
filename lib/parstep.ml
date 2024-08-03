open Printf

module Stack = Lockfree_stack
module HT = Lockfree_hashtable

type 'a chunk = {
    v : 'a array;
    mutable i : int;
}

type 'a worker_context_shared = {
    quit : bool Atomic.t;
    abort : bool Atomic.t;
    mutable num_rendezvous : int;
    mutable turn : bool;
    mutable step : int;
    mutex : Mutex.t;
    cv_rendezvous : Condition.t;
    cv_director : Condition.t;
    mutable vs_in : 'a chunk Lockfree_stack.t array;
    mutable vs_out : 'a chunk Lockfree_stack.t array;
    num_workers : int;
    mutable total_count : int;
    chunk_size : int;
    dummy_task : 'a;
    do_work : 'a worker_context -> unit;
}

and 'a worker_context = {
    id : int;
    shared : 'a worker_context_shared;
    mutable chunk_in : 'a chunk;
    mutable chunk_out : 'a chunk;
    mutable count : int;
}

let make_chunk chunk_size dummy_task = {
    v = Array.make chunk_size dummy_task;
    i = 0;
  }

let make_worker_context_shared num_workers chunk_size dummy_task do_work =
  {
    quit = Atomic.make false;
    abort = Atomic.make false;
    num_rendezvous = 0;
    turn = false;
    step = 0;
    mutex = Mutex.create ();
    cv_rendezvous = Condition.create ();
    cv_director = Condition.create ();
    vs_in = Array.init num_workers (fun _ -> Lockfree_stack.make ());
    vs_out = Array.init num_workers (fun _ -> Lockfree_stack.make ());
    num_workers;
    total_count = 0;
    chunk_size; dummy_task; do_work
  }

let make_worker_context id shared chunk_size dummy_task = {
    id;
    shared;
    chunk_in = make_chunk chunk_size dummy_task;
    chunk_out = make_chunk chunk_size dummy_task;
    count = 0;
}

let abort (xc : 'a worker_context) =
  Atomic.set xc.shared.abort true

let rec get (xc : 'a worker_context) =
  if Atomic.get xc.shared.abort then
    begin
      Printf.printf "%d aware abort\n" xc.id;
      None
    end
  else
    let i = xc.chunk_in.i in
    if i > 0 then
      begin
        let x = xc.chunk_in.v.(i - 1) in
        xc.chunk_in.i <- i - 1;
        Some x
      end
    else
      match Stack.pop xc.shared.vs_in.(xc.id) with
        Some chunk ->
         xc.chunk_in <- chunk;
         get xc
      | None ->
         let n = xc.shared.num_workers in
         let rec loop i k =
           match Stack.pop xc.shared.vs_in.(k) with
             Some chunk ->
              xc.chunk_in <- chunk;
              get xc
           | None ->
              if i=0 then
                None
              else
                loop (i-1) (if k=0 then n-1 else k-1)
         in
         loop (n-1) (if xc.id = 0 then n-1 else xc.id - 1)

let alloc_chunk (xc : 'a worker_context) =
  make_chunk xc.shared.chunk_size xc.shared.dummy_task

let rec put (xc : 'a worker_context) (x : 'a) =
  let c = xc.chunk_out in
  if c.i < Array.length c.v then
    begin
      c.v.(c.i) <- x;
      c.i <- c.i + 1;
      xc.count <- xc.count + 1
    end
  else
    let sh = xc.shared in
    Stack.push sh.vs_out.(xc.id) c;
    xc.chunk_out <- alloc_chunk xc;
    put xc x

let worker (xc : 'a worker_context) =
  let sh = xc.shared in
  let rec loop turn =
    Mutex.lock sh.mutex;
    sh.num_rendezvous <- sh.num_rendezvous + 1;
    if sh.num_rendezvous = sh.num_workers then
      Condition.signal sh.cv_director;

    while turn = sh.turn do
      Condition.wait sh.cv_rendezvous sh.mutex;
    done;
    Mutex.unlock sh.mutex;

    if Atomic.get sh.quit then
      ()
    else
      begin
        xc.count <- 0;
        sh.do_work xc;
        let tmp = xc.chunk_in in
        xc.chunk_in <- xc.chunk_out;
        xc.chunk_out <- tmp;
        loop (not turn)
      end
  in
  loop false

let make_list n f =
  let rec loop acc n =
    if n=0 then
      acc
    else
      loop ((f (n-1))::acc) (n-1)
  in
  loop [] n

let make_array n f =
  Array.of_list (make_list n f)

let parstep ?(b_progress = false) num_workers chunk_size dummy_task do_work =
  let shared = make_worker_context_shared
                 num_workers chunk_size dummy_task do_work in
  let v =
    make_array num_workers
      (fun id ->
        make_worker_context id shared chunk_size dummy_task)
  in

  v.(0).chunk_in.i <- 1;

  Mutex.lock shared.mutex;
  let pv =
    make_array num_workers
      (fun i -> Domain.spawn (fun () -> worker v.(i)))
  in
  
  while shared.num_rendezvous < num_workers do
    Condition.wait shared.cv_director shared.mutex
  done;

  let rec loop () =
    shared.num_rendezvous <- 0;
    shared.turn <- not shared.turn;
    Condition.broadcast shared.cv_rendezvous;
    while shared.num_rendezvous < num_workers do
      Condition.wait shared.cv_director shared.mutex
    done;

    if b_progress then
      begin
        printf "%d" shared.step;
        Array.iter (fun (xc : 'a worker_context) -> printf " | %d" xc.count) v;
        printf "\n"; flush stdout;
      end;

    let count =
      Array.fold_left
        (fun acc (xc : 'a worker_context) -> acc + xc.count)
        0 v
    in
    if count = 0 || Atomic.get shared.abort then
      ()
    else
      let tmp = shared.vs_in in
      shared.total_count <- shared.total_count + count;
      shared.vs_in <- shared.vs_out;
      shared.vs_out <- tmp;
      shared.step <- shared.step + 1;
      loop ()
  in

  loop ();
  Atomic.set shared.quit true;
  shared.turn <- not shared.turn;
  Condition.broadcast shared.cv_rendezvous;
  Mutex.unlock shared.mutex;
  Array.iter (fun p -> let _ = Domain.join p in ()) pv
