let dsize = 256
let bits = Sys.int_size

let d1 = dsize * bits
let d2 = dsize * d1

type t = {
    mutable v : int array option array option array option;
    mutable n : int;
  }

let cardinal s = s.n

let make () = { v = None; n = 0 }

let mem x (s : t) =
  let i = x / d2 in
  assert (0 <= i && i < dsize);
  match s.v with
    None -> false
  | Some v1 ->
     match v1.(i) with
       None -> false
     | Some v2 ->
        let y = x - i * d2 in
        let j = y / d1 in
        match v2.(j) with
          None -> false
        | Some v3 ->
           let z = y - j * d1 in
           let k = z / bits in
           let w = v3.(k) in
           let b = z - k * bits in
           w land (1 lsl b) <> 0

let add x (s : t) =
  let i = x / d2 in
  assert (0 <= i && i < dsize);
  let v1 : int array option array option array =
    match s.v with
      Some v1 -> v1
    | None ->
       let v1 = Array.make dsize None in
       s.v <- Some v1; v1
  in
  let v2 : int array option array =
    match v1.(i) with
      Some v2 -> v2
    | None ->
       let v2 = Array.make dsize None in
       v1.(i) <- Some v2; v2
  in
  let y = x - i * d2 in
  let j = y / d1 in
  let v3 : int array =
    match v2.(j) with
      Some v3 -> v3
    | None ->
       let v3 = Array.make dsize 0 in
       v2.(j) <- Some v3; v3
  in
  let z = y - j * d1 in
  let k = z / bits in
  let w = v3.(k) in
  let l = z - k * bits in
  let b = 1 lsl l in
  if w land b = 0 then
    (v3.(k) <- w lor b;
     s.n <- s.n + 1)

let equal (a : t) (b : t) =
  let eq2 x y =
    match x, y with
      Some u, Some v ->
       Array.for_all2 (=) u v
    | None, None -> true
    | _, _ -> false
  in
  let eq1 x y =
    match x, y with
      Some u, Some v ->
       Array.for_all2 eq2 u v
    | None, None -> true
    | _, _ -> false
  in
  if a.n <> b.n then
    false
  else
    match a.v, b.v with
      Some u, Some v ->
       Array.for_all2 eq1 u v
    | None, None -> true
    | _, _ -> false

let iter f (s : t) =
  match s.v with
    None -> ()
  | Some v1 ->
     for i=0 to dsize - 1 do
       match v1.(i) with
         None -> ()
       | Some v2 ->
          for j=0 to dsize - 1 do
            match v2.(j) with
              None -> ()
            | Some v3 ->
               for k=0 to dsize-1 do
                 let w = v3.(k) in
                 for l=0 to bits-1 do
                   if (w land (1 lsl l)) <> 0 then
                     f (l + bits * (k + dsize * (j + dsize * i)))
                 done
               done
          done
     done

let fold f s acc =
  let r = ref acc in
  iter (fun x -> r := f x !r) s;
  !r

let hash s = fold (+) s 0

let anatomy (s : t) =
  match s.v with
    None -> ()
  | Some v1 ->
     for i=0 to dsize - 1 do
       match v1.(i) with
         None -> ()
       | Some v2 ->
          Printf.printf "%d\n" i;
          for j=0 to dsize - 1 do
            match v2.(j) with
              None -> ()
            | Some v3 ->
               Printf.printf "  %d\n" j;
               for k=0 to dsize-1 do
                 let w = v3.(k) in
                 if w <> 0 then
                   Printf.printf "    %d %X\n" k w;
               done
          done
     done
