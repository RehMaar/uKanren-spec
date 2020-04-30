module L = List

open GT
open OCanren
open Std
open Nat
open TesterO

open UnifyTerm

(*open FuluUnify
open MaxuUnify
open MinuUnify
open NrcuUnify
open RanuUnify
open RecuUnify
open SequUnify
*)

(* a : nat, b : nat, q36 : bool *)
let rec eq_nat a b q36 =
  fresh (q37) (q37 === (pair a b))
    (conde
       [(q37 === (pair zero zero)) &&& (q36 === (!! true));
       fresh (q39) (q37 === (pair (succ q39) zero)) (q36 === (!! false));
       fresh (q41) (q37 === (pair zero (succ q41))) (q36 === (!! false));
       fresh (x y) (q37 === (pair (succ x) (succ y))) (eq_nat x y q36)])

(* var : nat, subst : (nat option) list, q32: nat option *)
let rec get_term var subst q32 =
  ((subst === (nil ())) &&& (q32 === (none ()))) ||| 
    (fresh (x xs)
      (subst === (x % xs)) 
      (((var === zero) &&& (x === q32)) ||| (fresh (n) (var === (succ n)) (get_term n xs q32))))

(* subst: (nat option) list, l1, l2: term list, q0: bool *)
let rec forall2 subst l1 l2 q0 =
    fresh (q1) (q1 === (pair l1 l2))
      (((q1 === (pair (nil ()) (nil ()))) &&& (q0 === (!! true))) |||
         (fresh (x xs y ys q3 q4) (q1 === (pair (x % xs) (y % ys))) 
          (check_uni subst x y q3)
            (forall2 subst xs ys q4) (conde [(q3 === (!! false)) &&& (q0 === (!! false)); (q3 === (!! true)) &&& (q0 === q4)])))
and
(* subst: term  list, t1: term, t2: term, q31: term *)
 check_uni subst t1 t2 q31 =
  fresh (q11) (q11 === (pair t1 t2))
    (conde
       [fresh (n1 a1 n2 a2 q12 q13)
          (q11 === (pair (constr n1 a1) (constr n2 a2)))
          (eq_nat n1 n2 q12)
          (forall2 subst a1 a2 q13)
          (conde [(q12 === (!! false)) &&& (q31 === (!! false)); (q12 === (!! true)) &&& (q31 === q13)]);
        fresh (v n a q19)
           (q11 === (pair (var_ v) (constr n a)))
           (get_term v subst q19)
           (((q19 === (none ())) &&& (q31 === (!! false))) ||| (fresh (t) (q19 === (some t)) (check_uni subst t t2 q31)));
        fresh (n a v q22)
           (q11 === (pair (constr n a) (var_ v)))
           (get_term v subst q22)
           (((q22 === (none ())) &&& (q31 === (!! false))) ||| (fresh (t) (q22 === (some t)) (check_uni subst t1 t q31)));
        fresh (v1 v2 q25)
           (q11 === (pair (var_ v1) (var_ v2)))
           (get_term v1 subst q25)
           ((fresh (t1') (q25 === (some t1')) (check_uni subst t1' t2 q31)) ||| (fresh (q27) (q25 === (none ())) (get_term v2 subst q27) ((fresh (q28) (q27 === (some q28)) (q31 === (!! false))) ||| ((q27 === (none ())) &&& (eq_nat v1 v2 q31)))))])

let onat x = nat (of_int x)

let v n           = var_ (onat n)
let c n a         = constr (onat n) (List.list a)


type term = ((OCanren.Std.Nat.ground, 'a OCanren.Std.List.ground) UnifyTerm.uterm as 'a, 
             (OCanren.Std.Nat.logic, 'b OCanren.Std.List.logic) UnifyTerm.uterm OCanren.logic as 'b) Logic.injected

let runOrig t1 t2 = 
  run q (fun q -> check_uni q t1 t2 (!!true)) (fun x -> x)


let runMthd mthd t1 t2 = run q (fun q -> mthd q t1 t2) (fun x -> x)

let runTimeTest x msg result = 
  let tx = Sys.time() in
  let answ = RStream.take ~n:x result in
  let t2 = Sys.time() in
  Printf.printf msg (t2 -. tx)
  
let runOn c x y = 
  Printf.printf "------\n%!";
  (*runTimeTest c "Orig: %f\n%!" @@ runOrig x y;*)
(*  runTimeTest c "SU : %f\n%!" @@ runMthd sequUnify x y;
  runTimeTest c "MnU: %f\n%!" @@ runMthd minuUnify x y;
  runTimeTest c "FU : %f\n%!" @@ runMthd fuluUnify x y;
  runTimeTest c "MxU: %f\n%!" @@ runMthd maxuUnify x y;
  runTimeTest c "NU : %f\n%!" @@ runMthd nrcuUnify x y;
  runTimeTest c "RcU: %f\n%!" @@ runMthd recuUnify x y;*)
  Printf.printf "------\n%!"

let t1 : term = c 0 [v 0; c 1 []]
let t1' : term = c 0 [c 1 []; v 0]

let (t2 : term), (t2' : term) =
  let appendo x y z = c 1 [x; y; z] in
  let cons x y = c 2 [x; y] in
  let nil = c 3 [] in
  let list2 x y = cons x (cons y nil) in
  let cA = c 4 [] in
  let cB = c 5 [] in
  let cC = c 6 [] in
  let cD = c 7 [] in
  let vX = v 0 in
  let vXs = v 1 in
  let vYs = v 2 in
  let vZs = v 3 in
  let vLs = v 4 in
  appendo (list2 cA cB) (list2 cC cD) (vLs),        
  appendo (cons vX vXs) (vYs)         (cons vX vZs) 

(* append([a, b]  , [c, d], Ls      ) *)
(* append([X | Xs], Ys    , [X | Zs]) *)


let (t3 : term), (t3' : term) =
  let f x y z = c 0 [x; y; z] in
  let g x y   = c 1 [x; y] in
  let p       = c 2 [] in
  let t       = c 3 [] in
  let x       = v 0 in
  let y       = v 1 in
  let l       = v 2 in
  let z       = v 3 in
  f x x (g z t),
  f (g p l) y y

(*let _ = 
  runOn 1 t1 t1';
  runOn 1 t2 t2';
  runOn 1 t3 t3'*)

(*let _ = run q (fun q -> check_uni q t1 t1' (!!true)) (fun d -> d)*)

let runL n = runR gunif_reifier show_runif show_lunif n

let _ = 
  runL 1  q qh (REPR (fun q -> t1 t1' !!true));
