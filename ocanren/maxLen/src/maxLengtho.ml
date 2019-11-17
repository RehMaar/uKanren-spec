module L = List

open GT
open OCanren
open Std
open Nat

let topLevelSU2 x0 x1 x2 =
  let rec maxLengtho y0 y1 y2 =
    fresh (q1 q2 q3) (y0 === nil () &&& (y2 === zero) &&& (y1 === zero) ||| (y0 === q1 % q2 &&& (y2 === succ q3) &&& (maxo1 (q1 % q2) y1 &&& lengtho q2 q3)))
  and maxo1 y3 y4 = fresh (q1 q2 q3) (y3 === nil () &&& (y4 === zero) ||| (y3 === zero % q1 &&& maxo1 q1 y4 ||| (y3 === succ q2 % q3 &&& _maxo1 q3 q2 y4)))
  and _maxo1 y5 y6 y7 =
    fresh (q1 q2 q3 q4 q5)
      ( y5 === nil ()
      &&& (y7 === succ y6)
      ||| ( y5 === q1 % q2
          &&& (_maxo1 q2 y6 y7 &&& (q1 === zero ||| (q1 === succ q3 &&& leo q3 y6)))
          ||| (y5 === succ q4 % q5 &&& (_maxo1 q5 q4 y7 &&& gto q4 y6)) ) )
  and leo y8 y9 = fresh (q1 q2) (y8 === zero ||| (y8 === succ q1 &&& (y9 === succ q2) &&& leo q1 q2))
  and gto y10 y11 = fresh (q1 q2 q3) (y10 === succ q1 &&& (y11 === zero) ||| (y10 === succ q2 &&& (y11 === succ q3) &&& gto q2 q3))
  and lengtho y12 y13 = fresh (q1 q2 q3) (y12 === nil () &&& (y13 === zero) ||| (y12 === q1 % q2 &&& (y13 === succ q3) &&& lengtho q2 q3)) in
  maxLengtho x0 x1 x2

let topLevelMy3 x0 x1 x2 =
  let rec maxLengtho y0 y1 y2 =
    fresh (q1 q2 q3) (y0 === nil () &&& (y2 === zero) &&& (y1 === zero) ||| (y0 === q1 % q2 &&& (y2 === succ q3) &&& (maxo1 (q1 % q2) y1 &&& lengtho q2 q3)))
  and maxo1 y3 y4 = fresh (q1 q2 q3) (y3 === nil () &&& (y4 === zero) ||| (y3 === zero % q1 &&& maxo1 q1 y4 ||| (y3 === succ q2 % q3 &&& _maxo1 q3 q2 y4)))
  and _maxo1 y5 y6 y7 =
    fresh (q1 q2 q3 q4 q5)
      ( y5 === nil ()
      &&& (y7 === succ y6)
      ||| ( y5 === q1 % q2
          &&& (_maxo1 q2 y6 y7 &&& (q1 === zero ||| (q1 === succ q3 &&& leo q3 y6)))
          ||| (y5 === succ q4 % q5 &&& (_maxo1 q5 q4 y7 &&& gto q4 y6)) ) )
  and leo y8 y9 = fresh (q1 q2) (y8 === zero ||| (y8 === succ q1 &&& (y9 === succ q2) &&& leo q1 q2))
  and gto y10 y11 = fresh (q1 q2 q3) (y10 === succ q1 &&& (y11 === zero) ||| (y10 === succ q2 &&& (y11 === succ q3) &&& gto q2 q3))
  and lengtho y12 y13 = fresh (q1 q2 q3) (y12 === nil () &&& (y13 === zero) ||| (y12 === q1 % q2 &&& (y13 === succ q3) &&& lengtho q2 q3)) in
  maxLengtho x0 x1 x2

let topLevelSU x0 x1 x2 =
  let rec maxLengtho y0 y1 y2 =
    fresh (q1 q2 q3) (y0 === nil () &&& (y2 === zero) &&& (y1 === zero) ||| (y0 === q1 % q2 &&& (y2 === succ q3) &&& (maxo1 (q1 % q2) y1 &&& lengtho q2 q3)))
  and maxo1 y3 y4 = fresh (q1 q2 q3) (y3 === nil () &&& (y4 === zero) ||| (y3 === zero % q1 &&& maxo1 q1 y4 ||| (y3 === succ q2 % q3 &&& _maxo1 q3 q2 y4)))
  and _maxo1 y5 y6 y7 =
    fresh (q1 q2 q3 q4 q5)
      ( y5 === nil ()
      &&& (y7 === succ y6)
      ||| ( y5 === q1 % q2
          &&& (_maxo1 q2 y6 y7 &&& (q1 === zero ||| (q1 === succ q3 &&& leo q3 y6)))
          ||| (y5 === succ q4 % q5 &&& (_maxo1 q5 q4 y7 &&& gto q4 y6)) ) )
  and leo y8 y9 = fresh (q1 q2) (y8 === zero ||| (y8 === succ q1 &&& (y9 === succ q2) &&& leo q1 q2))
  and gto y10 y11 = fresh (q1 q2 q3) (y10 === succ q1 &&& (y11 === zero) ||| (y10 === succ q2 &&& (y11 === succ q3) &&& gto q2 q3))
  and lengtho y12 y13 = fresh (q1 q2 q3) (y12 === nil () &&& (y13 === zero) ||| (y12 === q1 % q2 &&& (y13 === succ q3) &&& lengtho q2 q3)) in
  maxLengtho x0 x1 x2


let topLevelCPD x0 x1 x2 =
  let rec maxLengtho y0 y1 y2 =
    fresh (q1 q2 q3 q4)
      ( y0 === nil () &&& (y1 === zero) &&& (y2 === zero)
      ||| (y0 === zero % q1 &&& (y2 === succ q2) &&& maxo1Lengtho y1 q1 q2)
      ||| (y0 === succ q3 % q4 &&& (y2 === succ q2) &&& _maxo1Lengtho y1 q3 q4 q2) )
  and maxo1Lengtho y3 y4 y5 =
    fresh (q1 q2 q3 q4)
      ( y4 === nil () &&& (y3 === zero) &&& (y5 === zero)
      ||| (y4 === zero % q1 &&& (y5 === succ q2) &&& maxo1Lengtho y3 q1 q2)
      ||| (y4 === succ q3 % q4 &&& (y5 === succ q2) &&& _maxo1Lengtho y3 q3 q4 q2) )
  and _maxo1Lengtho y6 y7 y8 y9 =
    fresh (q1 q2 q3 q4 q5 q6)
      ( y8 === nil () &&& (y6 === succ y7) &&& (y9 === zero)
      ||| (y8 === q1 % q2 &&& (y9 === succ q3) &&& (_maxo1Lengtho y6 y7 q2 q3 &&& _leo q1 (succ y7)))
      ||| (y8 === succ q4 % q5 &&& (y9 === succ q6) &&& (_maxo1Lengtho y6 q4 q5 q6 &&& gto q4 y7)) )
  and _leo y12 y13 = fresh (q1 q2) (y12 === zero ||| (y12 === succ q1 &&& (y13 === succ q2) &&& _leo q1 q2))
  and gto y14 y15 = fresh (q1 q2 q3) (y14 === succ q1 &&& (y15 === zero) ||| (y14 === succ q2 &&& (y15 === succ q3) &&& gto q2 q3)) in
  maxLengtho x0 x1 x2

let x1 = ocanren([1; 0; 0; 1])

let result1 = run qr (fun q r -> topLevelCPD x1 q r) (fun c d -> (c, d))
let result2 = run qr (fun q r -> topLevelSU x1 q r) (fun c d -> (c, d))

let _ = 
       (*Printf.printf "CPD: %d\n" (L.length @@ Stream.take result1);*)
       L.iter (fun (c, d) -> Printf.printf "CPD: (%s, %s)\n"
                  (show(Nat.logic) @@ c#reify  (Nat.reify))
                  (show(Nat.logic) @@ d#reify  (Nat.reify))
               )
               @@  Stream.take result1;
        (*Printf.printf "My: %d\n" (L.length @@ Stream.take result2);*)
        L.iter (fun (c, d) -> Printf.printf "My:  (%s, %s)\n"
                  (show(Nat.logic) @@ c#reify  (Nat.reify))
                  (show(Nat.logic) @@ d#reify  (Nat.reify))
               )
               @@  Stream.take result2;

(*
let _ =
   let t1 = Sys.time() in
   let x = Stream.take ~n:10 result_resd in
   let t2 = Sys.time() in
   Printf.printf "%fs\n" (t2 -. t1);
   L.iter (fun c -> Printf.printf "%s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify)) @@ x
*)
