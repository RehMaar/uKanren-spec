(*
Запрос: Path.query1.
*)


module L = List

open GT
open OCanren
open Std
open Nat

(* Test eqNat *)

(*
The same code!

let topLevelCPD x0 x1 x2 =
  let rec eqNat y0 y1 y2 =
    fresh (q1 q2 q3 q4)
      ( y0 === zero &&& (y1 === zero) &&& (y2 === !!true)
      ||| (y0 === s q1 &&& (y1 === zero) &&& (y2 === !!false))
      ||| (y0 === zero &&& (y1 === s q2) &&& (y2 === !!false))
      ||| (y0 === s q3 &&& (y1 === s q4) &&& eqNat q3 q4 y2) )
  in
  eqNat x0 x1 x2*)

let topLevelMy x0 x1 x2 =
  let rec eqNat y0 y1 y2 =
    fresh (q1 q2 q3 q4)
      ( y0 === zero &&& (y1 === zero) &&& (y2 === !!true)
      ||| (y0 === s q1 &&& (y1 === zero) &&& (y2 === !!false)
      ||| (y0 === zero &&& (y1 === s q2) &&& (y2 === !!false) 
      ||| (y0 === s q3 &&& (y1 === s q4) &&& eqNat q3 q4 y2)) ) )
  in
  eqNat x0 x1 x2

let one = succ zero

let result_eq_nat1 = run q (fun q -> topLevelMy zero q (!!true)) id
let result_eq_nat2 = run q (fun q -> topLevelMy q one (!!true)) id
let result_eq_nat3 = run q (fun q -> topLevelMy one one q) id
let result_eq_nat4 = run q (fun q -> topLevelMy one zero q) id
let result_eq_nat5 = run q (fun q -> topLevelMy one q (!!false)) id

let _ = Printf.printf "Test eqNat\n-----------\n";
        L.iter (fun c -> Printf.printf "zero == x    -> %s\n"
                        @@ show(Nat.logic)
						@@ c#reify (Nat.reify))
        @@ Stream.take result_eq_nat1;
       L.iter (fun c -> Printf.printf "x == one     -> %s\n"
                        @@ show(Nat.logic)
						@@ c#reify (Nat.reify))
        @@ Stream.take result_eq_nat2;
       L.iter (fun c -> Printf.printf "one == one?  -> %s\n"
                        @@ show(Bool.logic)
						@@ c#reify (Bool.reify))
        @@ Stream.take result_eq_nat3;
       L.iter (fun c -> Printf.printf "one == zero? -> %s\n"
                        @@ show(Bool.logic)
						@@ c#reify (Bool.reify))
        @@ Stream.take result_eq_nat4;
       L.iter (fun c -> Printf.printf "x != one     -> %s\n"
                        @@ show(Nat.logic)
						@@ c#reify (Nat.reify))
        @@ Stream.take result_eq_nat5

(* Test eqPair *)

let topLevelCPD x0 x1 x2 =
  let rec eqPair y0 y1 y2 =
    fresh (q1 q2 q3 q4 q5)
      ( y0 === pair q1 q2
      &&& (y1 === pair q3 q4)
      &&& (y2 === !!false)
      &&& (_eqNat q1 q3 !!false &&& _eqNat q2 q4 q5)
      ||| (y0 === pair q1 q2 &&& (y1 === pair q3 q4) &&& (__eqNat q1 q3 &&& _eqNat q2 q4 y2)) )
  and _eqNat y5 y6 y7 =
    fresh (q1 q2 q3 q4)
      ( y5 === zero &&& (y6 === zero) &&& (y7 === !!true)
      ||| (y5 === s q1 &&& (y6 === zero) &&& (y7 === !!false))
      ||| (y5 === zero &&& (y6 === s q2) &&& (y7 === !!false))
      ||| (y5 === s q3 &&& (y6 === s q4) &&& _eqNat q3 q4 y7) )
  and __eqNat y8 y9 = fresh (q1 q2) (y8 === zero &&& (y9 === zero) ||| (y8 === s q1 &&& (y9 === s q2) &&& __eqNat q1 q2)) in
  eqPair x0 x1 x2

let topLevelMy x0 x1 x2 =
  let rec eqPair y0 y1 y2 =
    fresh (q1 q2 q3 q4)
      ( y0 === pair q1 q2
      &&& (y1 === pair q3 q4)
      &&& (y2 === !!false) &&& eqNatEqNat q1 q3 q2 q4
      ||| (y0 === pair q1 q2 &&& (y1 === pair q3 q4) &&& _eqNatEqNat q1 q3 q2 q4 y2) )
  and eqNatEqNat y3 y4 y5 y6 =
    fresh (q1 q2 q3 q4 q5)
      ( y3 === s q1 &&& (y4 === zero) &&& eqNat y5 y6 q2
      ||| (y3 === zero &&& (y4 === s q3) &&& eqNat y5 y6 q2 ||| (y3 === s q4 &&& (y4 === s q5) &&& eqNatEqNat q4 q5 y5 y6)) )
  and eqNat y8 y9 y10 =
    fresh (q1 q2 q3 q4)
      ( y8 === zero &&& (y9 === zero) &&& (y10 === !!true)
      ||| ( y8 === s q1 &&& (y9 === zero) &&& (y10 === !!false)
          ||| (y8 === zero &&& (y9 === s q2) &&& (y10 === !!false) ||| (y8 === s q3 &&& (y9 === s q4) &&& eqNat q3 q4 y10)) ) )
  and _eqNatEqNat y11 y12 y13 y14 y15 =
    fresh (q1 q2) (y11 === zero &&& (y12 === zero) &&& eqNat y13 y14 y15 ||| (y11 === s q1 &&& (y12 === s q2) &&& _eqNatEqNat q1 q2 y13 y14 y15))
  in
  eqPair x0 x1 x2

let result_eq_pair1 = run q (fun q -> topLevelMy (pair one zero) q (!!true)) id
let result_eq_pair11 = run q (fun q -> topLevelCPD (pair one zero) q (!!true)) id

let result_eq_pair2  = run q (fun q -> topLevelMy   (pair one zero) (pair one zero) q) id
let result_eq_pair22 = run q (fun q -> topLevelCPD (pair one zero) (pair one zero) q) id

let result_eq_pair3  = run q (fun q -> topLevelMy   (pair one zero) (pair one one) q) id
let result_eq_pair33 = run q (fun q -> topLevelCPD (pair one zero) (pair one one) q) id

let result_eq_pair4  = run q (fun q -> topLevelMy   (pair one zero) q (!!false)) id
let result_eq_pair44 = run q (fun q -> topLevelCPD (pair one zero) q (!!false)) id

let _ = Printf.printf "\nTest eqPair\n-----------\n";
        L.iter (fun c -> Printf.printf "SU:  (one, zero) == x -> %s\n"
                        @@ show(Pair.logic) (show(Nat.logic)) (show(Nat.logic))
						@@ c#reify (Pair.reify Nat.reify Nat.reify))
        @@ Stream.take result_eq_pair1;
        L.iter (fun c -> Printf.printf "CPD: (one, zero) == x -> %s\n"
                        @@ show(Pair.logic) (show(Nat.logic)) (show(Nat.logic))
						@@ c#reify (Pair.reify Nat.reify Nat.reify))
        @@ Stream.take result_eq_pair11;
        L.iter (fun c -> Printf.printf "SU:  (one, zero) == (one, zero) -> %s\n"
                        @@ show(Bool.logic)
						@@ c#reify (Bool.reify))
        @@ Stream.take result_eq_pair2;
        L.iter (fun c -> Printf.printf "CPD: (one, zero) == (one, zero) -> %s\n"
                        @@ show(Bool.logic)
						@@ c#reify (Bool.reify))
        @@ Stream.take result_eq_pair22;
        L.iter (fun c -> Printf.printf "SU:  (one, zero) == (one, one) -> %s\n"
                        @@ show(Bool.logic)
						@@ c#reify (Bool.reify))
        @@ Stream.take result_eq_pair3;
        L.iter (fun c -> Printf.printf "CPD: (one, zero) == (one, one) -> %s\n"
                        @@ show(Bool.logic)
						@@ c#reify (Bool.reify))
        @@ Stream.take result_eq_pair33;
        L.iter (fun c -> Printf.printf "SU:  (one, zero) != x -> %s\n"
                        @@ show(Pair.logic) (show(Nat.logic)) (show(Nat.logic))
						@@ c#reify (Pair.reify Nat.reify Nat.reify))
        @@ Stream.take result_eq_pair4;
        L.iter (fun c -> Printf.printf "CPD: (one, zero) != x -> %s\n"
                        @@ show(Pair.logic) (show(Nat.logic)) (show(Nat.logic))
						@@ c#reify (Pair.reify Nat.reify Nat.reify))
        @@ Stream.take result_eq_pair44

(* Test elem *)

let topLevelCPD x0 x1 x2 =
  let rec elem y0 y1 y2 =
    fresh (q1 q2 q3 q4 q5 q6)
      ( y1 === nil () &&& (y2 === !!false)
      ||| (y1 === pair q1 q2 % q3 &&& (y2 === !!true) &&& (y0 === pair q4 q5) &&& (__eqNat q4 q1 !!true &&& __eqNat q5 q2 !!true))
      ||| (y1 === q6 % q3 &&& eqPairElem y0 y2 q6 q3) )
  and eqPairElem y7 y8 y9 y10 =
    fresh (q1 q2 q3 q4 q5)
      ( y7 === pair q1 q2
      &&& (y9 === pair q3 q4)
      &&& (___eqNat q1 q3 &&& __eqNat q2 q4 q5 &&& elem (pair q1 q2) y10 y8)
      ||| (y7 === pair q1 q2 &&& (y9 === pair q3 q4) &&& (__eqNat q1 q3 !!true &&& ___eqNat q2 q4 &&& elem (pair q1 q2) y10 y8)) )
  and __eqNat y11 y12 y13 =
    fresh (q1 q2 q3 q4)
      ( y11 === zero &&& (y12 === zero) &&& (y13 === !!true)
      ||| (y11 === s q1 &&& (y12 === zero) &&& (y13 === !!false))
      ||| (y11 === zero &&& (y12 === s q2) &&& (y13 === !!false))
      ||| (y11 === s q3 &&& (y12 === s q4) &&& __eqNat q3 q4 y13) )
  and ___eqNat y14 y15 =
    fresh (q1 q2 q3 q4) (y14 === s q1 &&& (y15 === zero) ||| (y14 === zero &&& (y15 === s q2)) ||| (y14 === s q3 &&& (y15 === s q4) &&& ___eqNat q3 q4))
  in
  elem x0 x1 x2

let topLevelSU x0 x1 x2 =
  let rec elem y0 y1 y2 =
    fresh (q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11)
      ( y1 === nil () &&& (y2 === !!false)
      ||| ( y1
          === pair q1 q2 % q3
          &&& (y2 === !!true)
          &&& (y0 === pair q4 q5 &&& eqNatEqNat q4 q1 q5 q2)
          ||| ( y1 === q6 % q7
              &&& ( elem y0 q7 y2
                  &&& ( y0 === pair q8 q9
                      &&& (q6 === pair q10 q11)
                      &&& _eqNatEqNat q8 q10 q9 q11
                      ||| (y0 === pair q8 q9 &&& (q6 === pair q10 q11) &&& __eqNatEqNat q8 q10 q9 q11) ) ) ) ) )
  and eqNatEqNat y3 y4 y5 y6 = fresh (q1 q2) (y3 === zero &&& (y4 === zero) &&& eqNat y5 y6 ||| (y3 === s q1 &&& (y4 === s q2) &&& eqNatEqNat q1 q2 y5 y6))
  and eqNat y7 y8 = fresh (q1 q2) (y7 === zero &&& (y8 === zero) ||| (y7 === s q1 &&& (y8 === s q2) &&& eqNat q1 q2))
  and _eqNatEqNat y9 y10 y11 y12 =
    fresh (q1 q2 q3 q4)
      ( y9 === s q1 &&& (y10 === zero) &&& _eqNat y11 y12
      ||| (y9 === zero &&& (y10 === s q2) &&& _eqNat y11 y12 ||| (y9 === s q3 &&& (y10 === s q4) &&& _eqNatEqNat q3 q4 y11 y12)) )
  and _eqNat y14 y15 =
    fresh (q1 q2 q3 q4)
      ( y14 === zero &&& (y15 === zero)
      ||| (y14 === s q1 &&& (y15 === zero) ||| (y14 === zero &&& (y15 === s q2) ||| (y14 === s q3 &&& (y15 === s q4) &&& _eqNat q3 q4))) )
  and __eqNatEqNat y17 y18 y19 y20 =
    fresh (q1 q2) (y17 === zero &&& (y18 === zero) &&& __eqNat y19 y20 ||| (y17 === s q1 &&& (y18 === s q2) &&& __eqNatEqNat q1 q2 y19 y20))
  and __eqNat y21 y22 =
    fresh (q1 q2 q3 q4) (y21 === s q1 &&& (y22 === zero) ||| (y21 === zero &&& (y22 === s q2) ||| (y21 === s q3 &&& (y22 === s q4) &&& __eqNat q3 q4)))
  in
  elem x0 x1 x2

let list = ocanren([(1, 1); (2, 2); (3, 3)])
let p1 = pair one one

let result_elem1 = run q (fun q -> topLevelSU q list (!!true)) id
let result_elem11 = run q (fun q -> topLevelCPD q list (!!true)) id

let result_elem2 = run q (fun q -> topLevelSU q list (!!false)) id
let result_elem22 = run q (fun q -> topLevelCPD q list (!!false)) id

let result_elem3 = run q (fun q -> topLevelSU p1 q (!!true)) id
let result_elem33 = run q (fun q -> topLevelCPD p1 q (!!true)) id

let _ = Printf.printf "\nTest elem\n-----------\n";
        L.iter (fun c -> Printf.printf "SU: x `elem` [(1,1), (2,2), (3, 3)]? -> %s\n"
                        @@ show(Pair.logic) (show(Nat.logic)) (show(Nat.logic))
						@@ c#reify (Pair.reify Nat.reify  Nat.reify))
        @@ Stream.take result_elem1;
        L.iter (fun c -> Printf.printf "CPD: x `elem` [(1,1), (2,2), (3, 3)]? -> %s\n"
                        @@ show(Pair.logic) (show(Nat.logic)) (show(Nat.logic))
						@@ c#reify (Pair.reify Nat.reify  Nat.reify))
        @@ Stream.take result_elem11;
        L.iter (fun c -> Printf.printf "SU: x `elem` [(1,1), (2,2), (3, 3)] -> %s\n"
                        @@ show(Pair.logic) (show(Nat.logic)) (show(Nat.logic))
						@@ c#reify (Pair.reify Nat.reify  Nat.reify))
        @@ Stream.take result_elem2;
        L.iter (fun c -> Printf.printf "CPD: x `elem` [(1,1), (2,2), (3, 3)] -> %s\n"
                        @@ show(Pair.logic) (show(Nat.logic)) (show(Nat.logic))
						@@ c#reify (Pair.reify Nat.reify  Nat.reify))
        @@ Stream.take result_elem22;
        L.iter (fun c -> Printf.printf "SU:  (1,1) `elem` x -> %s\n"
                        @@ show(List.logic) (show(Pair.logic) (show(Nat.logic)) (show(Nat.logic)))
						@@ c#reify (List.reify (Pair.reify Nat.reify  Nat.reify)))
        @@ Stream.take ~n:2 result_elem3;
        L.iter (fun c -> Printf.printf "CPD: (1,1) `elem` x -> %s\n"
                        @@ show(List.logic) (show(Pair.logic) (show(Nat.logic)) (show(Nat.logic)))
						@@ c#reify (List.reify (Pair.reify Nat.reify  Nat.reify)))
        @@ Stream.take ~n:2 result_elem33

(* Test isPath (x, y, true) *)

let topLevelCPD x0 x1 =
  let rec isPath y0 y1 = fresh (q1 q2 q3 q4) (y0 === nil () ||| (y0 === q1 % nil ()) ||| (y0 === q2 % (q3 % q4) &&& elemIsPath y1 q2 q3 q4))
  and elemIsPath y2 y3 y4 y5 =
    fresh (q1 q2 q3 q4)
      ( y2
      === pair q1 q2 % q3
      &&& (___eqNat y3 q1 !!true &&& ___eqNat y4 q2 !!true &&& isPath (y4 % y5) (pair q1 q2 % q3))
      ||| (y2 === q4 % q3 &&& (eqPairElem y3 y4 q4 q3 &&& isPath (y4 % y5) (q4 % q3))) )
  and eqPairElem y10 y11 y12 y13 =
    fresh (q1 q2 q3)
      (y12 === pair q1 q2 &&& (eqNatElem y13 y10 y11 q1 &&& ___eqNat y11 q2 q3) ||| (y12 === pair q1 q2 &&& (__eqNatElem y13 y10 y11 q1 &&& _____eqNat y11 q2)))
  and eqNatElem y14 y15 y16 y17 =
    fresh (q1 q2 q3 q4)
      ( y15 === s q1 &&& (y17 === zero)
      &&& _______elem y14 y16 (s q1)
      ||| (y15 === zero &&& (y17 === s q2) &&& _______elem y14 y16 zero)
      ||| (y15 === s q3 &&& (y17 === s q4) &&& _eqNatElem y14 y16 q3 q4) )
  and _eqNatElem y26 y27 y28 y29 =
    fresh (q1 q2 q3 q4)
      ( y28 === s q1 &&& (y29 === zero)
      &&& _______elem y26 y27 (s (s q1))
      ||| (y28 === zero &&& (y29 === s q2) &&& _______elem y26 y27 (s zero))
      ||| (y28 === s q3 &&& (y29 === s q4) &&& (_____eqNat q3 q4 &&& _______elem y26 y27 (s (s q3)))) )
  and _______elem y39 y40 y41 =
    fresh (q1 q2 q3 q4) (y39 === pair q1 q2 % q3 &&& (___eqNat y41 q1 !!true &&& ___eqNat y40 q2 !!true) ||| (y39 === q4 % q3 &&& eqPairElem y41 y40 q4 q3))
  and ___eqNat y42 y43 y44 =
    fresh (q1 q2 q3 q4)
      ( y42 === zero &&& (y43 === zero) &&& (y44 === !!true)
      ||| (y42 === s q1 &&& (y43 === zero) &&& (y44 === !!false))
      ||| (y42 === zero &&& (y43 === s q2) &&& (y44 === !!false))
      ||| (y42 === s q3 &&& (y43 === s q4) &&& ___eqNat q3 q4 y44) )
  and __eqNatElem y45 y46 y47 y48 =
    fresh (q1 q2) (y46 === zero &&& (y48 === zero) &&& _______elem y45 y47 zero ||| (y46 === s q1 &&& (y48 === s q2) &&& ___eqNatElem y45 y47 q1 q2))
  and ___eqNatElem y54 y55 y56 y57 =
    fresh (q1 q2)
      ( y56 === zero &&& (y57 === zero)
      &&& _______elem y54 y55 (s zero)
      ||| (y56 === s q1 &&& (y57 === s q2) &&& (___eqNat q1 q2 !!true &&& _______elem y54 y55 (s (s q1)))) )
  and _____eqNat y67 y68 =
    fresh (q1 q2 q3 q4) (y67 === s q1 &&& (y68 === zero) ||| (y67 === zero &&& (y68 === s q2)) ||| (y67 === s q3 &&& (y68 === s q4) &&& _____eqNat q3 q4))
  in
  isPath x0 x1


let topLevelSU x0 x1 =
  let rec isPath y0 y1 = fresh (q1 q2 q3 q4) (y0 === nil () ||| (y0 === q1 % nil () ||| (y0 === q2 % (q3 % q4) &&& (isPath (q3 % q4) y1 &&& elem q2 q3 y1))))
  and elem y2 y3 y4 =
    fresh (q1 q2 q3 q4 q5 q6 q7)
      ( y4
      === pair q1 q2 % q3
      &&& eqNatEqNat y2 q1 y3 q2
      ||| (y4 === q4 % q5 &&& (elem y2 y3 q5 &&& (q4 === pair q6 q7 &&& _eqNatEqNat y2 q6 y3 q7 ||| (q4 === pair q6 q7 &&& __eqNatEqNat y2 q6 y3 q7)))) )
  and eqNatEqNat y5 y6 y7 y8 = fresh (q1 q2) (y5 === zero &&& (y6 === zero) &&& eqNat y7 y8 ||| (y5 === s q1 &&& (y6 === s q2) &&& eqNatEqNat q1 q2 y7 y8))
  and eqNat y9 y10 = fresh (q1 q2) (y9 === zero &&& (y10 === zero) ||| (y9 === s q1 &&& (y10 === s q2) &&& eqNat q1 q2))
  and _eqNatEqNat y11 y12 y13 y14 =
    fresh (q1 q2 q3 q4)
      ( y11 === s q1 &&& (y12 === zero) &&& _eqNat y13 y14
      ||| (y11 === zero &&& (y12 === s q2) &&& _eqNat y13 y14 ||| (y11 === s q3 &&& (y12 === s q4) &&& _eqNatEqNat q3 q4 y13 y14)) )
  and _eqNat y16 y17 =
    fresh (q1 q2 q3 q4)
      ( y16 === zero &&& (y17 === zero)
      ||| (y16 === s q1 &&& (y17 === zero) ||| (y16 === zero &&& (y17 === s q2) ||| (y16 === s q3 &&& (y17 === s q4) &&& _eqNat q3 q4))) )
  and __eqNatEqNat y19 y20 y21 y22 =
    fresh (q1 q2) (y19 === zero &&& (y20 === zero) &&& __eqNat y21 y22 ||| (y19 === s q1 &&& (y20 === s q2) &&& __eqNatEqNat q1 q2 y21 y22))
  and __eqNat y23 y24 =
    fresh (q1 q2 q3 q4) (y23 === s q1 &&& (y24 === zero) ||| (y23 === zero &&& (y24 === s q2) ||| (y23 === s q3 &&& (y24 === s q4) &&& __eqNat q3 q4)))
  in
  isPath x0 x1

let loop = ocanren([(1, 1)])

let topLevelMyTest = topLevelSU

let result_cpd_1 = run q (fun q -> topLevelCPD q loop) id
let result_my_1 = run q (fun q -> topLevelMyTest q loop) id

let dag = ocanren([(1, 2); (2, 3)])

let result_cpd_2 = run q (fun q -> topLevelCPD q dag) id
let result_my_2 = run q (fun q -> topLevelMyTest q dag ) id

let g = ocanren([(1, 2); (2, 3); (3, 1)])

let result_cpd_3 = run q (fun q -> topLevelCPD q g) id
let result_my_3 = run q (fun q -> topLevelMyTest q g) id


let _ = Printf.printf "Test isPath x y true\n---------------------\n";
   L.iter (fun c -> Printf.printf "CPD loop: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
   @@ Stream.take ~n:4 result_cpd_1;
   L.iter (fun c -> Printf.printf "SU loop: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
   @@ Stream.take ~n:4 result_my_1;
   Printf.printf "\n";

   let x =  Stream.take result_cpd_2 in
   L.iter (fun c -> Printf.printf "CPD dag: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
   @@ x;
   (* On ~n:6 it never ends. *)
   let x =  Stream.take ~n:5 result_my_2 in
   L.iter (fun c -> Printf.printf "SU dag: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
   @@ x;
   Printf.printf "\n";

   L.iter (fun c -> Printf.printf "CPD g: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
   @@ Stream.take ~n:10 result_cpd_3;
   L.iter (fun c -> Printf.printf "SU g: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
   @@ Stream.take ~n:10 result_my_3
