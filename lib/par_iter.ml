let par_iter num_workers n f =
  let m = n / num_workers in
  let rec loop ps i =
    if i < num_workers then
      let c = if i = num_workers-1 then n - m  * (num_workers - 1) else m in
      let p = Domain.spawn (fun () -> f (i*m) (i*m+c-1)) in
      loop (p::ps) (i+1)
    else
      List.iter (fun p -> let _ = Domain.join p in ()) ps
  in
  loop [] 0
