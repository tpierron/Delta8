type neigh = Three | Four | E3 | Five_weak | Five | Six | Seven | Eight
exception Break

let shift v n =
  let w = Array.copy v in
  for i = 0 to 7 do
    w.(i) <- v.((i+n) mod 8)
  done;
  w

let flip v =
  let w = Array.copy v in
  for i = 0 to 7 do
    w.(i) <- v.(7-i)
  done;
  w

let is_minimal ngbh =
  try
    for k = 0 to 7 do
      let w = shift ngbh k in 
      if ngbh > w || ngbh > flip w then raise Break
    done;
    true
  with Break -> false

let valid ngbh =
  try
    for i = 0 to 6 do
      if ngbh.(i) = E3 && ngbh.((i+1) mod 8) = Six && ngbh.((i+7) mod 8) = Six then raise Break;
      if ngbh.(i) = E3 && List.mem ngbh.((i+1) mod 8) [Five; Five_weak; E3] then raise Break;
      if ngbh.(i) = E3 && List.mem ngbh.((i+7) mod 8) [Five; Five_weak; E3] then raise Break;
    done;
    true
  with Break -> false

let hcost ngb = match ngb with
    Three -> 60
  | Four -> 40
  | E3 -> 20
  | Five_weak -> 40
  | _ -> 0


let harsh_cost = Array.fold_left (fun x y -> x + hcost y) 0 

let gen_ngbh () =
  let res = ref [] in 
  let rec aux current i =
    if i = 8 then begin 
        if is_minimal current && valid current && harsh_cost current > 120 then res:=(Array.copy current) :: !res
      end
    else begin 
        aux current (i+1);
        current.(i) <- Four;
        aux current (i+1);
        current.(i) <- E3;
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
        current.(i) <- Three
      end
  in
  aux (Array.make 8 Three) 0;
  !res

let ngbh = gen_ngbh () 

let gen_adj ngbh =
  let typ = Array.make 8 false in 
  for i = 0 to 6 do
    if List.mem ngbh.(i) [E3; Five_weak] then begin
        typ.(i) <- true;
        typ.((i-1+ Array.length typ) mod Array.length typ) <- true;
      end;
  done;
  let res = ref [] in 
  let rec aux current i = 
    if i = 8 then res:=(Array.copy current) :: !res
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
  aux (Array.make 8 false) 0;
  !res 


let configs = List.rev_map (fun a -> List.rev_map (fun b -> (a,b)) (gen_adj a)) ngbh |> List.fold_left (fun x y -> List.rev_append y x) [] 

let cost ngb left right = match (ngb,left,right) with
    Three, None, None -> 0
  | Three, None, _ -> 30
  | Three, _, None -> 30
  | Three, _, _ -> 60
  | Four, Some Seven, Some Seven -> 40
  | Four, Some Seven, Some Eight -> 35
  | Four, Some Eight, Some Seven -> 35
  | Four, Some Eight, Some Eight -> 30
  | Four, Some Seven, None -> 5
  | Four, None, Some Seven -> 5
  | E3, _, _ -> 20
  | Five_weak, Some Six, Some Six -> 40
  | Five_weak, Some Five, Some Six -> 30
  | Five_weak, Some Five_weak, Some Six -> 30
  | Five_weak, Some Six, Some Five -> 30
  | Five_weak, Some Six, Some Five_weak -> 30
  | Five_weak, Some Five, _ -> 10
  | Five_weak, Some Five_weak, _ -> 10
  | Five_weak, _, Some Five -> 10
  | Five_weak, _, Some Five_weak -> 10
  | Five_weak, _, _ -> 15
  | _,_,_ -> 0

let next (ngbh, adj) i =
  if adj.((i+8) mod 8) then Some (ngbh.((i+9) mod 8)) else None

let prev (ngbh, adj) i =
  if adj.((i+15) mod 8) then Some (ngbh.((i+15) mod 8)) else None

let total_loss (ngbh, adj) =
  let res = ref 0 in
  for i = 0 to 7 do
    let (n,p) = (next (ngbh,adj) i, prev (ngbh,adj) i) in
    if ngbh.(i) = Three && next (ngbh, adj) i = None && List.mem ngbh.((i+9) mod 8) [Six; Seven; Eight] then res := !res - 25;
    if ngbh.(i) = Three && prev (ngbh, adj) i = None && List.mem ngbh.((i+7) mod 8) [Six; Seven; Eight] then res := !res - 25;
    res:= !res +  cost ngbh.(i) p n;
  done;
  !res

let is_weak (ngbh, adj) i = List.mem ngbh.((i+8) mod 8) [E3;Five_weak] || (List.mem ngbh.((i+8) mod 8) [Four; Three] && prev (ngbh,adj) i <> None && next (ngbh, adj) i <> None)

let is_semiweak (ngbh, adj) i = List.mem ngbh.((i+8) mod 8) [Four; Three] && ((prev (ngbh,adj) i = None) <> (next (ngbh, adj) i = None))

let nb_of cond = List.length (List.filter cond [0;1;2;3;4;5;6;7])

let is_reducible ((ngbh, adj) as g) =
  try
    (* C13 *)
    if nb_of (fun i -> List.mem ngbh.(i) [Five;Five_weak; E3]) = 5
       && nb_of (fun i -> ngbh.(i) = Six) = 3 then raise Break; 
    if nb_of (fun i -> List.mem ngbh.(i) [Five_weak; E3] && next g i = Some Six && prev g i = Some Six) >= 2
       && nb_of (fun i -> List.mem ngbh.(i) [Five_weak; E3]) = 4
       && nb_of (fun i -> List.mem ngbh.(i) [Five; Six]) = 4 then raise Break;
    (* C14 *)
    if nb_of (fun i -> is_weak g i && ngbh.(i) = Four) >= 4
       && nb_of (fun i -> ngbh.(i) = Seven) >= 1  then raise Break;
    if nb_of (fun i -> is_weak g i && ngbh.(i) = Four && (next g i = Some Seven || prev g i = Some Seven)) >= 3
       && nb_of (fun i -> List.mem ngbh.(i) [E3; Five_weak] && (next g i = Some Seven || prev g i = Some Seven)) >= 1  then raise Break; 
    (* C15 *)
    if nb_of (fun i -> ngbh.(i) = Three && is_weak g i) >= 1
       && nb_of (fun i -> List.mem ngbh.(i) [Five_weak; E3]) >= 3
       && nb_of (fun i -> ngbh.(i) = Six) >= 2 then raise Break; 
    (* C18 *)
    if nb_of (fun i -> is_weak g i && ngbh.(i) = Three) >= 2
       && nb_of (fun i -> List.mem ngbh.(i) [Three; Four; Five; E3; Five_weak]) >= 1 then raise Break; 
    (* C19 *)
    if nb_of (fun i -> is_weak g i && ngbh.(i) = Three) >= 1
       && nb_of (fun i -> is_semiweak g i && ngbh.(i) = Three) >= 1
       && nb_of (fun i -> ngbh.(i) = Four) >= 1
       && nb_of (fun i -> List.mem ngbh.(i) [Three; Four; Five; Five_weak; E3; Six; Seven]) >= 4 then raise Break;
    if nb_of (fun i -> is_weak g i && ngbh.(i) = Three) >= 1
       && nb_of (fun i -> is_semiweak g i && ngbh.(i) = Three) >= 1
       && nb_of (fun i -> List.mem ngbh.(i) [Three; Four; Five; E3; Five_weak]) >= 3
       && nb_of (fun i -> List.mem ngbh.(i) [Three; Four; Five; E3; Five_weak; Six]) >= 4 then raise Break;
    (* C20 *)
    if nb_of (fun i -> is_weak g i && ngbh.(i) = Three) >= 1
       && nb_of (fun i -> ngbh.(i) = Four) >= 2
       && nb_of (fun i -> List.mem ngbh.(i) [Five; E3; Five_weak]) >= 1
       && nb_of (fun i -> ngbh.(i) = Seven) >= 1 then raise Break;
    (* C21 *)
    if nb_of (fun i -> is_weak g i && ngbh.(i) = Three) >= 1
       && nb_of (fun i -> is_weak g i && ngbh.(i) = Four) >= 2
       && nb_of (fun i -> List.mem ngbh.(i) [Four; Five; Five_weak; E3; Six; Seven]) >= 3 then raise Break;
    (* C22 *)
    if nb_of (fun i -> is_semiweak g i && ngbh.(i) = Three) >= 3
       && nb_of (fun i -> ngbh.(i) = Seven) >= 1 then raise Break;
    if nb_of (fun i -> is_semiweak g i && ngbh.(i) = Three) >= 2
       && nb_of (fun i -> ngbh.(i) = Four) >= 2
       && nb_of (fun i -> ngbh.(i) = Seven) >= 1 then raise Break;
    for i = 0 to 7 do
      let p = prev g i and n = next g i in
      (* C1 *)
      if ngbh.(i) = Three && not (List.mem n [Some Eight; None]) then raise Break;
      if ngbh.(i) = Three && not (List.mem p [Some Eight; None]) then raise Break;
      if ngbh.(i) = Four && List.mem n [Some Six; Some Five; Some Five_weak; Some E3; Some Four; Some Three] then raise Break;
      if ngbh.(i) = Four && List.mem p [Some Six; Some Five; Some Five_weak; Some E3; Some Four; Some Three] then raise Break;
      (* C2 *) 
      if ngbh.(i) = Eight && n = Some Three && p = Some Three then raise Break;
      (* C4 *)
      if List.mem ngbh.(i) [Five; Five_weak] && List.mem n [Some Five; Some Five_weak] && List.mem p [Some Five; Some Five_weak] then raise Break;
      (* C14 *)
      if ngbh.(i) = Four && n = Some Seven && p = Some Seven && is_weak g (i+2) && ngbh.((i+2) mod 8) = Four && List.mem (prev g (i-1)) [Some Four; Some Five; Some Five_weak; Some E3] && nb_of (fun i -> List.mem ngbh.(i) [Four; Five; Five_weak; E3]) >= 4 then raise Break;
      if ngbh.(i) = Four && n = Some Seven && p = Some Seven && is_weak g (i+6) && ngbh.((i+6) mod 8) = Four && List.mem (next g (i+1)) [Some Four; Some Five; Some Five_weak; Some E3] && nb_of (fun i -> List.mem ngbh.(i) [Four; Five; Five_weak; E3]) >= 4 then raise Break;
      (* C15 *)
      if ngbh.(i) = Three && is_weak g i && List.mem ngbh.((i+3) mod 8) [Five_weak; E3] && List.mem ngbh.((i+5) mod 8) [Five_weak; E3] && List.mem ngbh.((i+2) mod 8) [Five_weak; E3; Five; Six] && List.mem ngbh.((i+6) mod 8) [Five_weak; E3; Five; Six] && ngbh.((i+4) mod 8) = Six then raise Break;
      (* C16 *)
      if adj = Array.make 8 true && ngbh.(i) = Three && is_weak g i && ngbh.((i+4) mod 8) = Four && is_weak g (i+4) && ngbh.((i+2) mod 8) = E3 && List.mem ngbh.((i+6) mod 8) [Five; E3; Five_weak] then raise Break;
      if adj = Array.make 8 true && ngbh.(i) = Three && is_weak g i && ngbh.((i+4) mod 8) = Four && is_weak g (i+4) && ngbh.((i+6) mod 8) = E3 && List.mem ngbh.((i+2) mod 8) [Five; E3; Five_weak] then raise Break;
      if adj = Array.make 8 true && ngbh.(i) = Three && is_weak g i && ngbh.((i+4) mod 8) = Four && is_weak g (i+4) && List.mem ngbh.((i+2) mod 8) [Five; E3; Five_weak] && List.mem ngbh.((i+6) mod 8) [Five; E3; Five_weak] && (ngbh.((i+5) mod 8) = Seven || ngbh.((i+3) mod 8) = Seven) then raise Break;
      (* C17 *)
      if ngbh.(i) = Three && is_weak g i && ngbh.((i+2) mod 8) = Four && is_weak g (i+2) && ngbh.((i+3) mod 8) = Seven then raise Break;
      if ngbh.(i) = Three && is_weak g i && ngbh.((i+6) mod 8) = Four && is_weak g (i+6) && ngbh.((i+5) mod 8) = Seven then raise Break;
      if ngbh.(i) = Three && is_weak g i && ngbh.((i+2) mod 8) = Four && is_weak g (i+2) && List.mem ngbh.((i+5) mod 8) [Five_weak; E3] && List.mem ngbh.((i+6) mod 8) [Five; Five_weak; E3; Six] && List.mem ngbh.((i+4) mod 8) [Five; Five_weak; E3; Six] then raise Break;
      if ngbh.(i) = Three && is_weak g i && ngbh.((i+6) mod 8) = Four && is_weak g (i+6) && List.mem ngbh.((i+3) mod 8) [Five_weak; E3] && List.mem ngbh.((i+2) mod 8) [Five; Five_weak; E3; Six] && List.mem ngbh.((i+4) mod 8) [Five; Five_weak; E3; Six] then raise Break;
      if ngbh.(i) = Three && is_weak g i && ngbh.((i+2) mod 8) = Four && is_weak g (i+2) && nb_of (fun i -> ngbh.(i) = E3) >= 1 && nb_of (fun i -> List.mem ngbh.(i) [E3; Five_weak]) >= 2 then raise Break;
      if ngbh.(i) = Three && is_weak g i && ngbh.((i+6) mod 8) = Four && is_weak g (i+6) && nb_of (fun i -> ngbh.(i) = E3) >= 1 && nb_of (fun i -> List.mem ngbh.(i) [E3; Five_weak]) >= 2 then raise Break;      
    done;
    false
  with Break -> true

let _ =
    if List.for_all (fun x -> total_loss x <= 120 || is_reducible x) configs then Printf.printf "Youhou!\n" else Printf.printf "Snif\n"
