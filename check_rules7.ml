type neigh7 = Four | S3 | S5 | Five_weak | Five | Six | Seven | Eight
exception Break

let shift v n =
  let w = Array.copy v in
  for i = 0 to 6 do
    w.(i) <- v.((i+n) mod 7)
  done;
  w

let flip v =
  let w = Array.copy v in
  for i = 0 to 6 do
    w.(i) <- v.(6-i)
  done;
  w

let is_minimal ngbh =
  try
    for k = 0 to 6 do
      let w = shift ngbh k in 
      if ngbh > w || ngbh > flip w then raise Break
    done;
    true
  with Break -> false

let valid ngbh =
  try
    for i = 0 to 6 do
      if ngbh.(i) = S5 && (ngbh.((i+1) mod 7) <> Seven || ngbh.((i+6) mod 7) <> Seven) then raise Break;
      if ngbh.(i) = S3 && not (List.mem ngbh.((i+1) mod 7) [Six; Seven; Eight] && List.mem ngbh.((i+6) mod 7) [Six; Seven; Eight]) then raise Break;
    done;
    true
  with Break -> false

let hcost ngb = match ngb with
    Four -> 30
  | S3 -> 20
  | S5 -> 12
  | Five_weak -> 30
  | _ -> 0


let harsh_cost = Array.fold_left (fun x y -> x + hcost y) 0 


let gen_ngbh () =
  let res = ref [] in 
  let rec aux current i =
    if i = 7 then begin 
        if is_minimal current && valid current && harsh_cost current > 60 then res:=(Array.copy current) :: !res
      end
    else begin 
        aux current (i+1);
        current.(i) <- S3;
        aux current (i+1);
        current.(i) <- S5;
        aux current (i+1);
        current.(i) <- Five_weak;
        aux current (i+1);
        current.(i) <- Five;
        aux current (i+1);
        current.(i) <- Six;
        aux current (i+1);
        current.(i) <- Seven;
        aux current (i+1);
        current.(i) <- Eight;
        aux current (i+1);
        current.(i) <- Four
      end
  in
  aux (Array.make 7 Four) 0;
  !res

let ngbh = gen_ngbh ()

let gen_adj ngbh =
  let typ = Array.make 7 false in 
  for i = 0 to 6 do
    if List.mem ngbh.(i) [S3; S5; Five_weak] then begin
        typ.(i) <- true;
        typ.((i-1+ Array.length typ) mod Array.length typ) <- true;
      end;
  done;
  let res = ref [] in 
  let rec aux current i = 
    if i = 7 then res:=(Array.copy current) :: !res
    else
      begin 
        current.(i) <- true;
        aux current (i+1);
        if not typ.(i) then begin
            current.(i) <- false;
            aux current (i+1)
          end
      end
  in 
  aux (Array.make 7 false) 0;
  !res 

let configs = List.map (fun a -> List.map (fun b -> (a,b)) (gen_adj a)) ngbh |> List.concat 

let cost ngb left right = match (ngb,left,right) with
    Four, Seven, Seven -> 30
  | Four, Seven, Eight -> 25
  | Four, Eight, Seven -> 25
  | Four, Eight, Eight -> 20
  | S3,_,_ -> 20
  | S5,_,_ -> 12
  | Five_weak, Six, Five -> 30
  | Five_weak, Six, Five_weak -> 30
  | Five_weak, Five, Six -> 30
  | Five_weak, Five_weak, Six -> 30
  | Five_weak, _, _ -> 10
  | _,_,_ -> 0

let next (ngbh, adj) i =
  if adj.((i+7) mod 7) then Some (ngbh.((i+8) mod 7)) else None

let prev (ngbh, adj) i =
  if adj.((i+13) mod 7) then Some (ngbh.((i+13) mod 7)) else None

let total_loss (ngbh, adj) =
  let res = ref 0 in
  for i = 0 to 6 do
    if ngbh.(i) = Six && next (ngbh, adj) i = None && List.mem ngbh.((i+8) mod 7) [Six; Seven; Eight] then res := !res - 20;
    if List.mem ngbh.(i) [Seven; Eight] && next (ngbh, adj) i = None && List.mem ngbh.((i+8) mod 7) [Seven; Eight] then res := !res - 5;
    res:= !res +
            match (next (ngbh,adj) i, prev (ngbh,adj) i) with
              None, _ -> 0
            | _, None -> 0
            | Some p, Some n -> cost ngbh.(i) p n;
                                
                                
  done;
  !res

let is_weak (ngbh, adj) i = List.mem ngbh.((i+7) mod 7) [S3;S5;Five_weak] || (ngbh.((i+7) mod 7) = Four && prev (ngbh,adj) i <> None && next (ngbh, adj) i <> None)

let is_not_reducible ((ngbh, adj) as g)=
  try
    for i = 0 to 6 do
      let p = prev g i and n = next g i in 
      (* C1 *)
      if ngbh.(i) = Four && List.mem n [Some Six; Some Five; Some Five_weak; Some S5; Some S3; Some Four] then raise Break;
      if ngbh.(i) = Four && List.mem p [Some Six; Some Five; Some Five_weak; Some S5; Some S3; Some Four] then raise Break;
      (* C2 *) 
      if ngbh.(i) = Seven && n = Some Four && p = Some Four then raise Break;
      (* C4 *)
      if List.mem ngbh.(i) [Five; Five_weak] && List.mem n [Some Five; Some Five_weak] && List.mem p [Some Five; Some Five_weak] then raise Break;
      (* C5 *)
      if ngbh.(i) = Five_weak && List.mem n [Some Five; Some Five_weak] && p = Some Six && List.mem (prev g (i-1)) [Some Five; Some Five_weak; Some S3]  then raise Break;
      if ngbh.(i) = Five_weak && List.mem p [Some Five; Some Five_weak] && n = Some Six && List.mem (next g (i+1)) [Some Five; Some Five_weak; Some S3]  then raise Break;
      if ngbh.(i) = Five_weak && p = Some Five_weak && n = Some Six && prev g (i-1) = Some Six  then raise Break;
      if ngbh.(i) = Six && p = Some Six && n = Some Five_weak && List.mem (next g (i+1)) [Some Five; Some Five_weak] && prev g (i-1) = Some Five_weak && List.mem (prev g (i-2)) [Some Five_weak; Some Five] then raise Break;
      (* C7 *)
      if ngbh.(i) = Five_weak && List.mem n [Some Five; Some Five_weak] && p = Some Six && Array.fold_left (fun x y -> x || y = Four) false ngbh then raise Break;
      if ngbh.(i) = Five_weak && List.mem p [Some Five; Some Five_weak] && n = Some Six && Array.fold_left (fun x y -> x || y = Four) false ngbh then raise Break;
      (* C8 *)
      if ngbh.(i) = Four && p <> None && n = Some Seven && next g (i+1) = Some S3 && Array.fold_left (fun x y -> x+ (if List.mem y [Five; Five_weak; S3; S5] then 1 else 0)) 0 ngbh >= 2 then raise Break;
      if ngbh.(i) = Four && n <> None && p = Some Seven && prev g (i-1) = Some S3 && Array.fold_left (fun x y -> x+ (if List.mem y [Five; Five_weak; S3; S5] then 1 else 0)) 0 ngbh >= 2 then raise Break;
      (* C9 *) 
      if List.mem ngbh.(i) [S3; S5] && is_weak g (i-2) && ngbh.((i+2) mod 7) = Four && is_weak g (i+2) && (next g (i+2) = Some Seven || prev g (i+2) = Some Seven) then raise Break;
      if List.mem ngbh.(i) [S3; S5] && is_weak g (i-2) && ngbh.((i+5) mod 7) = Four && is_weak g (i+2) && (next g (i+5) = Some Seven || prev g (i+5) = Some Seven) then raise Break;
      (* C10 *)
      if ngbh.(i) = Seven && List.length (List.filter (fun i -> ngbh.(i) = Four && is_weak g i) [0;1;2;3;4;5;6]) >= 3 then raise Break;
      (* C11 *)
      if ngbh.(i) = Four && is_weak g i && n = Some Seven && ngbh.((i+5) mod 7) = Four && is_weak g (i+5) && is_weak g (i+2) then raise Break;
      if ngbh.(i) = Four && is_weak g i && p = Some Seven && ngbh.((i+2) mod 7) = Four && is_weak g (i+5) && is_weak g (i+2) then raise Break;
      if ngbh.(i) = Four && is_weak g i && n = Some Seven && ngbh.((i+5) mod 7) = Four && is_weak g (i+5) && ngbh.((i+3) mod 7) = S3 then raise Break;
      if ngbh.(i) = Four && is_weak g i && p = Some Seven && ngbh.((i+2) mod 7) = Four && is_weak g (i+2) && ngbh.((i+4) mod 7) = S3 then raise Break;
      (* C12 *)
      if ngbh.(i) = Four && p = Some Seven && n = Some Seven && is_weak g (i+2) && ngbh.((i+4) mod 7) = Four && is_weak g  (i+4) then raise Break;
      if ngbh.(i) = Four && p = Some Seven && n = Some Seven && is_weak g (i+5) && ngbh.((i+3) mod 7) = Four && is_weak g  (i+3) then raise Break;
      if ngbh.(i) = Four && is_weak g i && n = Some Seven && is_weak g (i+2) && ngbh.((i+3) mod 7) = Seven && ngbh.((i+4) mod 7) = Four && is_weak g (i+4) then raise Break;
      if ngbh.(i) = Four && is_weak g i && p = Some Seven && is_weak g (i+5) && ngbh.((i+4) mod 7) = Seven && ngbh.((i+3) mod 7) = Four && is_weak g (i+3) then raise Break;
      if ngbh.(i) = Four && is_weak g i && (n = Some Seven || p = Some Seven) && ngbh.((i+2) mod 7) = S3 && ngbh.((i+4) mod 7) = Four && is_weak g (i+4) then raise Break;
      if ngbh.(i) = Four && is_weak g i && (p = Some Seven || n = Some Seven) && ngbh.((i+5) mod 7) = S3 && ngbh.((i+3) mod 7) = Four && is_weak g (i+3) then raise Break;
    done;
    true
  with Break -> false




let problems = List.filter (fun x -> total_loss x > 60 && is_not_reducible x) configs
