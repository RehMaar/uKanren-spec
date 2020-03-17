module L = List

open GT
open OCanren
open Std
open Nat

open FuluMaxLen
open SequMaxLen
open MaxuMaxLen
open MinuMaxLen
open NrcuMaxLen
open RanuMaxLen
open RecuMaxLen
open CpdMaxLen
open MaxLen

let x1 = ocanren([1;1;1;1;1;1;1;1;1;1])
let x2 = ocanren([1; 2; 3; 4; 5; 6; 7; 8; 9; 10])
let x3 = ocanren([1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 1; 2; 3; 4; 5])
let x4 = ocanren([1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15])

let result1 x = run qr (fun q r -> sequMaxLen x q r) (fun c d -> (c, d))
let result2 x = run qr (fun q r -> fuluMaxLen x q r) (fun c d -> (c, d))
let result3 x = run qr (fun q r -> maxuMaxLen x q r) (fun c d -> (c, d))
let result4 x = run qr (fun q r -> minuMaxLen x q r) (fun c d -> (c, d))
let result5 x = run qr (fun q r -> ranuMaxLen x q r) (fun c d -> (c, d))
let result6 x = run qr (fun q r -> recuMaxLen x q r) (fun c d -> (c, d))
let result7 x = run qr (fun q r -> nrcuMaxLen x q r) (fun c d -> (c, d))
let result8 x = run qr (fun q r -> cpdMaxLenOld x q r) (fun c d -> (c, d))
let result9 x = run qr (fun q r -> maxLen x q r) (fun c d -> (c, d))

let runTest name result = 
  Printf.printf "%s:%!" name;
  let t1 = Sys.time() in
  let x = Stream.take result in
  let t2 = Sys.time() in
  Printf.printf " %fs\n%!" (t2 -. t1);
(*  L.iter (fun (c, d) -> Printf.printf "A:  (%s, %s)\n%!"
            (show(Nat.logic) @@ c#reify  (Nat.reify))
            (show(Nat.logic) @@ d#reify  (Nat.reify))
         )
         @@  Stream.take result;*)
  ()

let run x =
  runTest "Orig " (result9 x);
  runTest "CPD  " (result8 x);
  (*runTest "SU   " (result1 x);*)
  (*runTest "FU   " (result2 x);*)
  (*runTest "MaxU " (result3 x);*)
  (*runTest "MinU " (result4 x);*)
  (*runTest "RandU" (result5 x);*)
  (*runTest "RecU " (result6 x);*)
  (*runTest "NRecU" (result7 x);*)
  Printf.printf "%!"

let _ =
  Printf.printf "|[1..1]| = 10\n%!";
  run x1;
  Printf.printf "|[1..10]| = 10\n%!";
  run x2;
  Printf.printf "|[1..10, 1..5]| = 15\n%!";
  run x3;
  Printf.printf "|[1..15]|\n%!";
  run x4;
  Printf.printf ""
(*
let _ =
   L.iter (fun c -> Printf.printf "%s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify)) @@ x
*)

(* Just to test that UnrecUnfold and RecUnfold work fine *)

(*
let topLevelMaxoRec x0 x1 =
  let rec maxo y0 y1 = maxo1 y0 y1
  and maxo1 y2 y3 = fresh (q1 q2 q3) (y2 === nil () &&& (y3 === zero) ||| (y2 === zero % q1 &&& maxo1 q1 y3 ||| (y2 === succ q2 % q3 &&& _maxo1 q3 q2 y3)))
  and _maxo1 y4 y5 y6 =
    fresh (q1 q2 q3 q4 q5)
      ( y4 === nil ()
      &&& (y6 === succ y5)
      ||| ( y4 === q1 % q2
          &&& (_maxo1 q2 y5 y6 &&& (q1 === zero ||| (q1 === succ q3 &&& leo q3 y5)))
          ||| (y4 === succ q4 % q5 &&& (_maxo1 q5 q4 y6 &&& gto q4 y5)) ) )
  and leo y7 y8 = fresh (q1 q2) (y7 === zero ||| (y7 === succ q1 &&& (y8 === succ q2) &&& leo q1 q2))
  and gto y9 y10 = fresh (q1 q2 q3) (y9 === succ q1 &&& (y10 === zero) ||| (y9 === succ q2 &&& (y10 === succ q3) &&& gto q2 q3)) in
  maxo x0 x1

let topLevelMaxoUn x0 x1 =
  let rec maxo y0 y1 = maxo1 y0 y1
  and maxo1 y2 y3 = fresh (q1 q2 q3) (y2 === nil () &&& (y3 === zero) ||| (y2 === zero % q1 &&& maxo1 q1 y3 ||| (y2 === succ q2 % q3 &&& _maxo1 q3 q2
y3)))
  and _maxo1 y4 y5 y6 =
    fresh (q1 q2 q3 q4 q5)
      ( y4 === nil ()
      &&& (y6 === succ y5)
      ||| ( y4 === q1 % q2
          &&& (_maxo1 q2 y5 y6 &&& (q1 === zero ||| (q1 === succ q3 &&& leo q3 y5)))
          ||| (y4 === succ q4 % q5 &&& (_maxo1 q5 q4 y6 &&& gto q4 y5)) ) )
  and leo y7 y8 = fresh (q1 q2) (y7 === zero ||| (y7 === succ q1 &&& (y8 === succ q2) &&& leo q1 q2))
  and gto y9 y10 = fresh (q1 q2 q3) (y9 === succ q1 &&& (y10 === zero) ||| (y9 === succ q2 &&& (y10 === succ q3) &&& gto q2 q3)) in
  maxo x0 x1


let resultMaxo = run q (fun q -> topLevelMaxoRec x1 q) (fun c -> c)
let _ = 
       Printf.printf "Maxo: %d\n" (L.length @@ Stream.take resultMaxo);
       L.iter (fun c -> Printf.printf "Maxo: %s\n"
                  (show(Nat.logic) @@ c#reify  (Nat.reify))
               )
               @@  Stream.take resultMaxo
*)

(*

let rec _lengtho y4 y5 =
     fresh (q1 q2 q3) (y4 === nil () &&& (y5 === zero) ||| (y4 === q1 % q2 &&& (y5 === succ q3) &&& _lengtho q2 q3))

let rec _leo y13 y14 =
     fresh (q1 q2) (y13 === zero ||| (y13 === succ q1 &&& (y14 === succ q2) &&& _leo q1 q2))
let rec leo y11 y12 =
     fresh (q1) (y11 === zero ||| (y11 === succ q1 &&& _leo q1 y12))

let rec gto y15 y16 =
     fresh (q1 q2 q3) (y15 === succ q1 &&& (y16 === zero ||| (y15 === succ q2 &&& (y16 === succ q3) &&& gto q2 q3)))

let rec _maxo1 y8 y9 y10 =
  fresh (q1 q2 q3 q4)
    ( y8 === nil ()
    &&& (y10 === succ y9)
    ||| (y8 === q1 % q2 &&& (_maxo1 q2 y9 y10 &&& leo q1 y9) 
    ||| (y8 === succ q3 % q4 &&& (_maxo1 q4 q3 y10 &&& gto q3 y9))) )
let rec maxo1 y6 y7 =
     fresh (q1 q2 q3) (y6 === nil () &&& (y7 === zero) ||| (y6 === zero % q1 &&& maxo1 q1 y7 ||| (y6 === succ q2 % q3 &&& _maxo1 q3 q2 y7)))



let one = ocanren(1)
let two = ocanren(2)

let res1 = run q (fun q -> _leo two q) (fun q -> q)

let _ = 
       L.iter (fun c -> Printf.printf "Maxo: %s\n"
                  (show(Nat.logic) @@ c#reify  (Nat.reify))
               )
               @@  Stream.take ~n:3 res1
*)

