(* The goal of this program is to check that if u is an 7-vertex with
  neighbors v_1, ..., v_7 in clockwise order, then u ends up with
  non-negative weight.
  
  We will generate all possible neighborhoods of u, and check in each
  case that either u has non-negative weight or some reducible
  configuration occurs *)
type neighbor = Four | S5 | S3 | Five_weak | Five | Six | Seven | Eight
(* The possible neighbor types are their degree, except for degree 5
  vertices (whose transfered weight does not depend only on the
  neighborhood of the 7-vertex) :
  - S3 is an S_3-neighbor
  - S5 is an S_5-neighbor
  - Five_weak is a weak 5-neighbor which is not S_3 nor S_5
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
  for i = 0 to 6 do
    w.(i) <- v.((i+n) mod 7)
  done; 
  w

(* flip v outputs the neighborhood obtained by applying a mirror symmetry to v *)
let flip v =
  let w = Array.copy v in
  for i = 0 to 6 do
    w.(i) <- v.(6-i)
  done; 
  w

(* In order to generate the values of ngbh up to symmetries, we will
  only keep the values that are minimal among all their rotations and
  symmetries. is_minimal tests if that is the case. *)
let is_minimal ngbh =
  try
    for k = 0 to 6 do
      let w = shift ngbh k in 
      if ngbh > w || ngbh > flip w then raise Break
    done; 
    true
  with Break -> false

(* Due to the definition of S3 and S5, if v_i is an S_5-neighbor, then
  v_{i+1} and v_{i-1} have degree 7, while if v_i is an S_3-neighbor,
  v_{i+1} and v_{i-1} have degree at least 6. The function valid
  tests whether ngbh satisfies this condition. *)
let valid ngbh =
  try
    for i = 0 to 6 do
      if ngbh.(i) = S5 && (ngbh.((i+1) mod 7) <> Seven || ngbh.((i+6) mod 7) <> Seven) then raise Break; 
      if ngbh.(i) = S3 && not (List.mem ngbh.((i+1) mod 7) [Six; Seven; Eight] && List.mem ngbh.((i+6) mod 7) [Six; Seven; Eight]) then raise Break; 
    done; 
    true
  with Break -> false

(* generation of the values of ngbh: we go through all the 8^7 cases,
  and keep only the minimal values that are valid and non trivially
  solved *)
let gen_ngbh () =
  let res = ref [] in 
  let rec aux current i =
    if i = 7 then begin 
        if is_minimal current && valid current then res:=(Array.copy current) :: !res
      end
    else List.iter (fun x -> aux current (i+1); current.(i) <- x) [S3; S5; Five_weak; Five; Six; Seven; Eight; Four]
  in
  aux (Array.make 7 Four) 0; 
  !res

let ngbh = gen_ngbh ()
let _ = Printf.printf "%d neighborhood types generated\n%!" (List.length ngbh)

(*****************************)
(* Generation of adjacencies *)
(*****************************)

(* Whenever we get an S3, S5 or Five_weak neighbor v_i, then the edges
  v_iv_{i+1} and v_{i-1}v_i must be present. Given a value ngbh, we
  generate all possible values of adj that satisfy this condition. *)
let gen_adj ngbh =
  let res = ref [] in 
  let rec aux current i = 
    if i = 7 then res:=(Array.copy current) :: !res
    else
      begin 
        current.(i) <- true; 
        aux current (i+1); 
        if not (List.mem ngbh.(i) [S3; S5; Five_weak])
           && not (List.mem ngbh.((i+1) mod 7) [S3; S5; Five_weak]) then begin
            current.(i) <- false; 
            aux current (i+1)
          end
      end
  in 
  aux (Array.make 7 false) 0; 
  !res 

(* We finally generate all configurations: for each ngbh, we generate
  all corresponding values of adj, and concatenate everything *)
let configs = List.map (fun a -> List.map (fun b -> (a,b)) (gen_adj a)) ngbh |> List.concat 
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
  if adj.((i+7) mod 7) then Some (ngbh.((i+8) mod 7)) else None

(* prev config i outputs Some t if v_iv_{i-1} is an edge and v_{i-1}
  has type t, and None otherwise *)
let prev (ngbh, adj) i =
  if adj.((i+13) mod 7) then Some (ngbh.((i+13) mod 7)) else None

(* cost computes the amount of weight given to a given v_i *)
let cost ngb left right = match (ngb,left,right) with
    (* R10 *)
    Four, Seven, Seven -> 30
  | Four, Seven, Eight -> 25
  | Four, Eight, Seven -> 25
  | Four, Eight, Eight -> 20
  (* R11 *)
  | Five_weak, Six, Five -> 30
  | Five_weak, Six, Five_weak -> 30
  | Five_weak, Five, Six -> 30
  | Five_weak, Five_weak, Six -> 30
  (* R12 *)
  | S3,_,_ -> 20
  (* R13 *)
  | S5,_,_ -> 12
  (* R14 *)
  | Five_weak, _, _ -> 10
  (* default *)
  | _,_,_ -> 0

(* The total loss of a configuration is the sum of the weights given
  to each v_i, minus the amount of weight received by R3. Note that
  R4 is not implemented since we cannot check its condition of
  application. *)
let total_loss (ngbh, adj) =
  let res = ref 0 in
  for i = 0 to 6 do
    (* R3 *)
    if ngbh.(i) = Six && next (ngbh, adj) i = None && List.mem ngbh.((i+8) mod 7) [Six; Seven; Eight] then res := !res - 20; 
    if List.mem ngbh.(i) [Seven; Eight] && next (ngbh, adj) i = None && ngbh.((i+8) mod 7) = Six then res := !res - 20; 
    if List.mem ngbh.(i) [Seven; Eight] && next (ngbh, adj) i = None && List.mem ngbh.((i+8) mod 7) [Seven; Eight] then res := !res - 5; 
    (* other rules (that apply only to weak neighbors) *)
    res:= !res +
            match (next (ngbh,adj) i, prev (ngbh,adj) i) with
              None, _ -> 0
            | _, None -> 0
            | Some p, Some n -> cost ngbh.(i) p n; 
  done; 
  !res

let unhappy = List.filter (fun x -> total_loss x > 60) configs
let _ = Printf.printf "%d configurations give too much weight\n%!" (List.length unhappy)

(************************)
(* Testing reducibility *)
(************************)

(* matches_aux tests whether its first argument is a sub-configuration
  of the second *)
let matches_aux (ngbh,adj) (pattern_n, pattern_a) =
  try
    for i = 0 to 6 do
      if ngbh.(i) > pattern_n.(i) then raise Break; 
      if pattern_a.(i) && not adj.(i) then raise Break
    done; 
    true
  with Break -> false

(* matches tests whether its first argument is a sub-configuration of
  the second, up to symmetries. *)
let matches config (pattern_n, pattern_a) =
  try
    for k = 0 to 6 do
      let w = shift pattern_n k in
      let w'= shift pattern_a k in 
      if matches_aux config (w,w') || matches_aux config (flip w, shift (flip w') 1) then raise Break
    done; 
    false
  with Break -> true

(* testing whether a neighbor is weak/semiweak *)
let is_weak (ngbh, adj) i = List.mem ngbh.((i+7) mod 7) [S3; S5; Five_weak] || (ngbh.((i+7) mod 7) = Four && prev (ngbh,adj) i <> None && next (ngbh, adj) i <> None)


(* Wrapping up to test whether a configuration of the neighborhood is
  reducible. *)
let is_not_reducible g=
  try
    (* C1 *)
    if matches g ([|Four; Six; Eight; Eight; Eight; Eight; Eight|],
                  [|true; false; false; false; false; false; false|]) then raise Break; 
    (* C2 *) 
    if matches g ([|Four; Seven; Four; Eight; Eight; Eight; Eight|],
                  [|true; true; false; false; false; false; false|]) then raise Break; 
    (* C4 *)
    if matches g ([|Five; Five; Five; Eight; Eight; Eight; Eight|],
                  [|true; true; false; false; false; false; false|]) then raise Break; 
    (* C5 *)
    if matches g ([|Five; Five_weak; Six; Five; Eight; Eight; Eight|],
                  [|true; true; true; false; false; false; false|]) then raise Break; 
    if matches g ([|Six; Five_weak; Five_weak; Six; Eight; Eight; Eight|],
                  [|true; true; true; false; false; false; false|]) then raise Break; 
    if matches g ([|Five; Five_weak; Six; Six; Five_weak; Five; Eight|],
                  [|true; true; true; true; true; false; false|]) then raise Break; 
    (* C7 *)
    if matches g ([|Six; Five_weak; Five; Four; Eight; Eight; Eight|],
                  [|true; true; false; false; false; false; false|]) then raise Break; 
    if matches g ([|Six; Five_weak; Five; Eight; Four; Eight; Eight|],
                  [|true; true; false; false; false; false; false|]) then raise Break; 
    if matches g ([|Six; Five_weak; Five; Eight; Eight; Four; Eight|],
                  [|true; true; false; false; false; false; false|]) then raise Break; 
    if matches g ([|Six; Five_weak; Five; Eight; Eight; Eight; Four|],
                  [|true; true; false; false; false; false; false|]) then raise Break; 
    (* C8 *)
    if matches g ([|S3; Seven; Four; Eight; Five; Eight; Eight|],
                  [|true; true; true; false; false; false; true|]) then raise Break; 
    if matches g ([|S3; Seven; Four; Eight; Eight; Five; Eight|],
                  [|true; true; true; false; false; false; true|]) then raise Break; 
    (* C9 *) 
    if matches g ([|Seven; Four; Eight; S3; Eight; Five_weak; Eight|],
                  [|true; true; true; true; true; true; false|]) then raise Break; 
    if matches g ([|Eight; Four; Seven; S3; Eight; Five_weak; Eight|],
                  [|true; true; true; true; true; true; false|]) then raise Break; 
    (* C10 *)
    if matches g ([|Eight; Four; Eight; Four; Eight; Four; Seven|],
                  [|true; true; true; true; true; true; false|]) then raise Break; 
    (* C11 *)
    if matches g ([|Eight; Four; Eight; Four; Seven; Five_weak; Eight|],
                  [|true; true; true; true; true; true; false|]) then raise Break; 
    if matches g ([|Eight; Four; Eight; Four; Seven; Eight; S3|],
                  Array.make 7 true) then raise Break; 
    (* C12 *)
    if matches g ([|Seven; Four; Seven; Five_weak; Eight; Four; Eight|],
                  [|true; true; true; true; true; true; false|]) then raise Break; 
    if matches g ([|Eight; Four; Seven; Five_weak; Seven; Four; Eight|],
                  [|true; true; true; true; true; true; false|]) then raise Break; 
    if matches g ([|Eight; Four; Seven; S3; Eight; Four; Eight|],
                  [|true; true; true; true; true; true; false|]) then raise Break; 
    if matches g ([|Seven; Four; Eight; S3; Eight; Four; Eight|],
                  [|true; true; true; true; true; true; false|]) then raise Break; 
    true
  with Break -> false


(*******************)
(* The final check *)
(*******************)

let to_string = function 
    Four -> "4"
  | S5 -> "S5"
  | S3 -> "S3"
  | Five_weak -> "5w"
  | Five -> "5"
  | Six -> "6"
  | Seven -> "7"
  | Eight -> "8"

let print (ngbh, adj) =
  for i = 0 to 6 do
    Printf.printf "%s " (to_string ngbh.(i)); 
    if adj.(i) then Printf.printf "-- " else Printf.printf "  "
  done; 
  Printf.printf "\n\n%!"

(* This should output two configurations, for which R4 allows to conclude. *)
let final = List.filter is_not_reducible unhappy

let _ = Printf.printf "Among them, %d are not reducible, namely: \n%!" (List.length final); 
        List.iter print final; 
        Printf.printf "R4 should apply to make the final weight non-negative in these cases. Please check the article.\n"
