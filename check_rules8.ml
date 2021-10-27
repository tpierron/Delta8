(* The goal of this program is to check that if u is an 8-vertex with
   neighbors v_1, ..., v_8 in clockwise order, then u ends up with
   non-negative weight.
   
   We will generate all possible neighborhoods of u, and check in each
   case that either u has non-negative weight or some reducible
   configuration occurs *)

type neighbor = Three | Four | E3 | Five_weak | Five | Six | Seven | Eight 
(* The possible neighbor types are their degree, except for degree 5
   vertices (whose transfered weight does not depend only on the
   neighborhood of the 8-vertex) :
   - E3 is an E_3-neighbor
   - Five_weak is a weak 5-neighbr which is not E_3
   - Five is a non-weak 5-neighbor *)

exception Break


(***********************************)
(* Generation of the neighborhoods *)
(***********************************)

(* A neighborhood is given by
   
   - a vector ngbh of size 8 such that ngbh.(i) contains the type of v_{i-1}
   - a boolean vector adj of size 8 such that adj.(i) is true whenever v_{i-1}v_i is an edge
   
   We first generate all possible values of ngbh up to symmetries and
   rotations, then filter some out, and only then, generate the
   corresponding adj. *)

(* shift v n outputs the neighborhood obtained by rotating v by n positions *)
let shift v n =
  let w = Array.copy v in
  for i = 0 to 7 do
    w.(i) <- v.((i+n) mod 8)
  done;
  w

(* flip v outputs the neighborhood obtained by applying a mirror symmetry to v *)
let flip v =
  let w = Array.copy v in
  for i = 0 to 7 do
    w.(i) <- v.(7-i)
  done;
  w

(* In order to generate the values of ngbh up to symmetries, we will
   only keep the values that are minimal among all their rotations and
   symmetries. is_minimal tests if that is the case. *)
let is_minimal ngbh =
  try
    for k = 0 to 7 do
      let w = shift ngbh k in 
      if ngbh > w || ngbh > flip w then raise Break
    done;
    true
  with Break -> false

(* Due to the definition of E3, if v_i is an E3-neighbor, then none of
   v_{i+1} and v_{i-1} can have degree 5, and both cannot have degree
   6. The function valid tests whether ngbh satisfies this
   condition. *)
let valid ngbh =
  try
    for i = 0 to 7 do
      if ngbh.(i) = E3 && ngbh.((i+1) mod 8) = Six && ngbh.((i+7) mod 8) = Six then raise Break;
      if ngbh.(i) = E3 && List.mem ngbh.((i+1) mod 8) [Five; Five_weak; E3] then raise Break;
      if ngbh.(i) = E3 && List.mem ngbh.((i+7) mod 8) [Five; Five_weak; E3] then raise Break;
    done;
    true
  with Break -> false

(* In order to reduce the number of possible configurations, we
   compute a harsh upper bound on the weight loss, and filter out the
   values of ngbh for which this upper bound is already too small.
   
   Note that, in order to avoid floating point errors, we scaled all
   weights by 60, so that all weight transfers become integers.  *)
let hcost ngb = match ngb with
    Three -> 60 (* worst case from R5 and R6 *)
  | Four -> 40 (* worst case from R7 and R8 *) 
  | E3 -> 20 (* R9 *) 
  | Five_weak -> 40 (* worst case from R9 *)
  | _ -> 0 

(* harsh_cost computes the aforementioned upper bound on the weight loss *) 
let harsh_cost = Array.fold_left (fun x y -> x + hcost y) 0 

(* generation of the values of ngbh: we go through all the 8^8 cases,
   and keep only the minimal values that are valid and non trivially
   solved *)
let gen_ngbh () =
  let res = ref [] in 
  let rec aux current i =
    if i = 8 then begin 
        if is_minimal current && valid current && harsh_cost current > 120 then res:=(Array.copy current) :: !res
      end
    else List.iter (fun x -> aux current (i+1); current.(i) <- x) [Four; E3; Five_weak; Five; Six; Seven; Eight; Three]
  in
  aux (Array.make 8 Three) 0;
  !res

let ngbh = gen_ngbh () 
let _ = Printf.printf "%d neighborhood types generated\n%!" (List.length ngbh)

(*****************************)
(* Generation of adjacencies *)
(*****************************)

(* Whenever we get an E3 or Five_weak neighbor v_i, then the edges
   v_iv_{i+1} and v_{i-1}v_i must be present. Given a value ngbh, we
   generate all possible values of adj that satisfy this condition. *)
let gen_adj ngbh =
  let res = ref [] in 
  let rec aux current i = 
    if i = 8 then res:=(Array.copy current) :: !res
    else
      begin 
        current.(i) <- true;
        aux current (i+1);
        if not (List.mem ngbh.(i) [E3; Five_weak]) && not (List.mem ngbh.((i+1) mod 8) [E3; Five_weak]) then begin
            current.(i) <- false;
            aux current (i+1)
          end
      end
  in 
  aux (Array.make 8 false) 0;
  !res 

(* We finally generate all configurations: for each ngbh, we generate
   all corresponding values of adj, and concatenate everything *)
let configs = List.rev_map (fun a -> List.rev_map (fun b -> (a,b)) (gen_adj a)) ngbh |> List.fold_left (fun x y -> List.rev_append y x) []
let _ = Printf.printf "%d configurations generated\n%!" (List.length configs)

(**********************)
(* Applying the rules *)
(**********************)

(* We now have enough information to compute exactly the weight
   loss. For each v_i, the amount of weight transfered from u to v_i
   depends only on the type of v_i, the type of v_{i-1} if v_{i-1}v_i
   is an edge, and similarly for v_{i+1}. *)

(* next config i outputs Some t if v_iv_{i+1} is an edge and v_{i+1}
   has type t, and None otherwise *)
let next (ngbh, adj) i =
  if adj.((i+8) mod 8) then Some (ngbh.((i+9) mod 8)) else None

(* prev config i outputs Some t if v_iv_{i-1} is an edge and v_{i-1}
   has type t, and None otherwise *)
let prev (ngbh, adj) i =
  if adj.((i+15) mod 8) then Some (ngbh.((i+15) mod 8)) else None

(* cost computes the amount of weight given to a given v_i *)
let cost ngb left right = match (ngb,left,right) with
  (* R5 *) 
  | Three, Some _, Some _ -> 60
  (* R6 *)
  | Three, None, Some _ -> 30 
  | Three, Some _, None -> 30 
  (* R7 *)
  | Four, Some Seven, Some Seven -> 40 
  | Four, Some Seven, Some Eight -> 35 
  | Four, Some Eight, Some Seven -> 35 
  | Four, Some Eight, Some Eight -> 30
  (* R8 *)
  | Four, Some Seven, None -> 5
  | Four, None, Some Seven -> 5
  (* R9 *)
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
  (* default *)
  | _,_,_ -> 0

(* The total loss of a configuration is the sum of the weights given
   to each v_i, minus the amount of weight received by R2 *)
let total_loss (ngbh, adj) =
  let res = ref 0 in
  for i = 0 to 7 do
    let (n,p) = (next (ngbh,adj) i, prev (ngbh,adj) i) in
    (* R2 *)
    if ngbh.(i) = Three && next (ngbh, adj) i = None && List.mem ngbh.((i+9) mod 8) [Six; Seven; Eight] then res := !res - 25;
    if ngbh.(i) = Three && prev (ngbh, adj) i = None && List.mem ngbh.((i+7) mod 8) [Six; Seven; Eight] then res := !res - 25;
    (* other rules *)
    res:= !res +  cost ngbh.(i) p n;
  done;
  !res

let unhappy =  List.filter (fun x -> total_loss x > 120) configs
let _ = Printf.printf "%d configurations give too much weight\n%!" (List.length unhappy)

(************************)
(* Testing reducibility *)
(************************)

(* matches_aux tests whether its first argument is a sub-configuration
   of the second *)
let matches_aux (ngbh,adj) (pattern_n, pattern_a) =
  try
    for i = 0 to 7 do
      if ngbh.(i) > pattern_n.(i) then raise Break;
      if pattern_a.(i) && not adj.(i) then raise Break
    done;
    true
  with Break -> false

(* matches tests whether its first argument is a sub-configuration of
   the second, up to symmetries. This will be useful for
   configurations C1-C17. *)
let matches config (pattern_n, pattern_a) =
  try
    for k = 0 to 7 do
      let w = shift pattern_n k in
      let w'= shift pattern_a k in 
      if matches_aux config (w,w') || matches_aux config (flip w, shift (flip w') 1) then raise Break
    done;
    false
  with Break -> true

(* Configurations C18-C22 rely on counting the number of vertices with
   degree and weakness conditions. We provide such primitives. *)
(* testing whether a neighbor is weak/semiweak *)
let is_weak (ngbh, adj) i =
  List.mem ngbh.(i) [E3;Five_weak]
  || (List.mem ngbh.(i) [Four; Three] && prev (ngbh,adj) i <> None && next (ngbh, adj) i <> None)

let is_semiweak (ngbh, adj) i =
  List.mem ngbh.(i) [Four; Three]
  && ((prev (ngbh,adj) i = None) <> (next (ngbh, adj) i = None))

(* counting the number of (weak/semiweak) neighbors of type at most c
   (types are sorted in the order given at the beginning *)
let nb_of c (ngbh,_) =  List.length (List.filter (fun i -> ngbh.(i) <= c) [0;1;2;3;4;5;6;7])
let nb_of_weak c ((ngbh,_) as g) =  List.length (List.filter (fun i -> is_weak g i && ngbh.(i) <= c) [0;1;2;3;4;5;6;7])
let nb_of_semiweak c ((ngbh,_) as g) =  List.length (List.filter (fun i -> is_semiweak g i && ngbh.(i) <= c) [0;1;2;3;4;5;6;7])


(* Wrapping up to test whether a configuration of the neighborhood is
   reducible. *)
let is_not_reducible g =
  try
    (* C1 *)
    if matches g ([|Three;Seven;Eight;Eight;Eight;Eight;Eight;Eight|],
                  [|true;false;false;false;false;false;false;false|]) then raise Break;
    if matches g ([|Four;Six;Eight;Eight;Eight;Eight;Eight;Eight|],
                  [|true;false;false;false;false;false;false;false|]) then raise Break;
    (* C2 *) 
    if matches g ([|Three;Eight;Three;Eight;Eight;Eight;Eight;Eight|],
                  [|true;true;false;false;false;false;false;false|]) then raise Break;
    (* C4 *)
    if matches g ([|Five;Five;Five;Eight;Eight;Eight;Eight;Eight|],
                  [|true;true;false;false;false;false;false;false|]) then raise Break;
    (* C13 *)
    if matches g ([|Six; Five_weak; Six; Five_weak; Six; Five_weak; Six; Five_weak|],
                  Array.make 8 true) then raise Break;
    if matches g ([|Six; Five_weak; Six; Five_weak; Six; Five_weak; Five_weak; Six|],
                  [|true;true;true;true;true;true;true;false|]) then raise Break;
    if matches g ([|Six; Five_weak; Six; Five_weak; Five_weak; Six; Five_weak; Six|],
                  [|true;true;true;true;true;true;true;false|]) then raise Break;
    (* C14 *)
    if matches g ([|Four; Seven; Four; Eight; Four; Eight; Four; Eight|],
                  Array.make 8 true) then raise Break;
    if matches g ([|Four; Seven; Four; Eight; Four; Seven; Five_weak; Eight|],
                  Array.make 8 true) then raise Break;
    if matches g ([|Four; Seven; Four; Eight; Five; Eight; Five; Seven|],
                  [|true;true;true;false;false;false;true;true|]) then raise Break;
    if matches g ([|Four; Seven; Four; Eight; Eight; Five; Five; Seven|],
                  [|true;true;true;false;false;false;true;true|]) then raise Break;      
    (* C15 *)
    if matches g ([|Eight; Three; Eight; Six; Five_weak; Six; Five_weak; Six|],
                  [|true;true;false;true;true;true;true;false|]) then raise Break;
    if matches g ([|Eight; Three; Eight; Five_weak; Six; Five_weak; Five_weak; Six|],
                  [|true;true;true;true;true;true;true;false|]) then raise Break;      
    if matches g ([|Eight; Three; Eight; Five_weak; Six; Five_weak; Six; Five_weak|],
                  Array.make 8 true) then raise Break;      
    (* C16 *)
    if matches g ([|Eight; Three; Eight; Five_weak; Eight; Four; Seven; Five_weak|],
                  Array.make 8 true) then raise Break;
    if matches g ([|Eight; Three; Eight; E3; Eight; Four; Eight; Five_weak|],
                  Array.make 8 true) then raise Break;      
    (* C17 *)
    if matches g ([|Eight; Three; Eight; Four; Seven; Eight; Eight; Eight|],
                  [|true;true;true;true;false;false;false;false|]) then raise Break;      
    if matches g ([|Eight; Three; Eight; Four; Eight; Six; Five_weak; Six|],
                  [|true;true;true;true;false;true;true;false|]) then raise Break;      
    if matches g ([|Eight; Three; Eight; Four; Eight; Five_weak; Six; Five_weak|],
                  Array.make 8 true) then raise Break;      
    if matches g ([|Eight; Three; Eight; Four; Eight; E3; Eight; Five_weak|],
                  Array.make 8 true) then raise Break;      
    if matches g ([|Eight; Three; Eight; Four; Eight; Five_weak; Eight; E3|],
                  Array.make 8 true) then raise Break;      
    (* C18 *)
    if nb_of_weak Three g >= 2 && nb_of Five g >= 3 then raise Break;
    (* C19 *)
    if nb_of_weak Three g >= 1 && nb_of_semiweak Three g >= 1
       && nb_of Four g >= 3 && nb_of Seven g >= 4 then raise Break;
    if nb_of_weak Three g >= 1 && nb_of_semiweak Three g >= 1
       && nb_of Five g >= 3 && nb_of Six g >= 4 then raise Break;
    (* C20 *)
    if nb_of_weak Three g >= 1 && nb_of Four g >= 3
       && nb_of Five g >= 4 && nb_of Seven g >= 5 then raise Break;
    (* C21 *)
    if nb_of_weak Three g >= 1 && nb_of_weak Four g >= 3 && nb_of Seven g >= 4 then raise Break;
    (* C22 *)
    if nb_of_semiweak Three g >= 3 && nb_of Seven g >= 4 then raise Break;
    if nb_of_semiweak Three g >= 2 && nb_of Four g >= 4 && nb_of Seven g >= 5 then raise Break;
    true
  with Break -> false


(*******************)
(* The final check *)
(*******************)

(* This should print 0 since all non-reducible configurations lose a
   weight of at most 120. *)
let _ = Printf.printf "among them, %d are not reducible\n%!" (List.length (List.filter is_not_reducible unhappy))

