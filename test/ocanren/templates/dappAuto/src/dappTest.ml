module L = List

open GT
open OCanren
open Std
open Nat

open MaxuDapp
open MinuDapp
open NrcuDapp
open RecuDapp
open SequDapp
open FuluDapp

let origDapp a b c d =
  let rec doubleAppendo y0 y1 y2 y3 = fresh (t) (appendo y0 y1 t &&& appendo t y2 y3)
  and appendo y4 y5 y6 =
    y4 === nil () &&& (y6 === y5) ||| fresh (ty t h) (y4 === h % t &&& (y6 === h % ty &&& appendo t y5 ty))
  in doubleAppendo a b c d

let cpdDapp x0 x1 x2 x3 =
  let rec doubleAppendo y0 y1 y2 y3 = fresh (q1 q2) (y0 === nil () &&& appendo y2 y3 y1 ||| (y0 === q1 % q2 &&& appendoAppendo y1 y2 y3 q1 q2))
  and appendo y4 y5 y6 = fresh (q1 q2 q3) (y6 === nil () &&& (y4 === y5) ||| (y6 === q1 % q2 &&& (y5 === q1 % q3) &&& appendo y4 q3 q2))
  and appendoAppendo y7 y8 y9 y10 y11 =
    fresh (q1 q2 q3) (y11 === nil () &&& appendo y8 y9 (y10 % y7) ||| (y11 === q1 % q2 &&& (appendo y7 q3 q2 &&& appendo y8 y9 (y10 % (q1 % q3)))))
  in
  doubleAppendo x0 x1 x2 x3


let runTimeTest msg stream = 
   let t1 = Sys.time() in
   let x = RStream.take stream in
   let t2 = Sys.time() in
   let time = t2 -. t1 in
   Printf.printf "%s: %f\n%!" msg time

let runTest msg stream = 
    L.iter (fun c -> Printf.printf "%s: %s\n%!" msg @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify)) 
    @@  Stream.take stream

let x11 = ocanren([1; 2])
let x12 = ocanren([3; 4])
let x13 = ocanren([5; 6])


let x21 = ocanren([1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
                   1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
                   1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
                   1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
                   1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
                   1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20])
let x22 = ocanren([1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
                   1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
                   1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
                   1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
                   1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
                   1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20])
let x23 = ocanren([1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
                   1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
                   1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
                   1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
                   1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
                   1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20])

let run topLevel a b c = run q (fun q -> topLevel a b c q) (fun c -> c)


let runTests =
  runTest "Orig" @@ run origDapp x11 x12 x13;
  runTest "CPD " @@ run cpdDapp x11 x12 x13;
  runTest "SU  " @@ run sequDapp x11 x12 x13;
  runTest "NU  " @@ run nrcuDapp x11 x12 x13;
  runTest "RU  " @@ run recuDapp x11 x12 x13;
  runTest "MxU " @@ run maxuDapp x11 x12 x13;
  runTest "MnU " @@ run minuDapp x11 x12 x13;
  runTest "FU  " @@ run fuluDapp x11 x12 x13

let runTimeTests =
  runTimeTest "Orig" @@ run origDapp x21 x22 x23;
  runTimeTest "CPD " @@ run cpdDapp  x21 x22 x23;
  runTimeTest "SU  " @@ run sequDapp x21 x22 x23;
  runTimeTest "NU  " @@ run nrcuDapp x21 x22 x23;
  runTimeTest "RU  " @@ run recuDapp x21 x22 x23;
  runTimeTest "MxU " @@ run maxuDapp x21 x22 x23;
  runTimeTest "MnU " @@ run minuDapp x21 x22 x23;
  runTimeTest "FU  " @@ run fuluDapp x21 x22 x23

let _ =
  runTests;
  runTimeTests
