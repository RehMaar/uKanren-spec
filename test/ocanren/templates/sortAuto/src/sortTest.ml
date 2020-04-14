module L = List

open GT
open Printf

open OCanren
open OCanren.Std
open Nat

open FuluSort
open SequSort
open NrcuSort
open RecuSort
open MinuSort
open MaxuSort

(* Original sorting program *)
let minmaxo a b min max =
  let open Nat in
  conde
    [ (min === a) &&& (max === b) &&& (a <= b)
    ; (max === a) &&& (min === b) &&& (a >  b)
    ]

let rec smallesto l s l' = conde
  [ (l === !< s) &&& (l' === nil())
  ; fresh (h t s' t' max)
      (l' === max % t')
      (l === h % t)
      (minmaxo h s' s max)
      (smallesto t s' t')
  ]

let rec sorto x y =
  conde
    [
      (x === nil()) &&& (y === nil())
    ; fresh (s xs xs')
        (y === s % xs')
        (smallesto x s xs)
        (sorto xs xs')    
    ]

(* Making regular sorting from relational one *)
let sort l =
  List.to_list Nat.to_int @@
    RStream.hd @@
      run q (sorto @@ nat_list l)
            (fun rr -> rr#prj)

let sortGen sortFn l =
  List.to_list Nat.to_int @@
    RStream.hd @@
      run q (sortFn @@ nat_list l)
            (fun rr -> rr#prj)

(************)
let sortOrig x0 x1 =
  let rec sorto y0 y1 =
    y0 === nil () &&& (y1 === nil ()) ||| fresh (xs' xs s) (y1 === s % xs' &&& (sorto xs xs' &&& smallesto y0 s xs))
  and smallesto y2 y3 y4 =
    y2
    === y3 % nil ()
    &&& (y4 === nil ())
    ||| fresh (max t' s' t h) (y4 === max % t' &&& (y2 === h % t &&& (minmaxo h s' y3 max &&& smallesto t s' t')))
  and minmaxo y5 y6 y7 y8 =
    y7 === y5 &&& (y8 === y6 &&& leo y5 y6 !!true) ||| (y8 === y5 &&& (y7 === y6 &&& gto y5 y6 !!true))
  and leo y9 y10 y11 =
    y9 === zero &&& (y11 === !!true)
    ||| ( fresh (zz) (y9 === succ zz &&& (y10 === zero &&& (y11 === !!false)))
        ||| fresh (y' x') (y9 === succ x' &&& (y10 === succ y' &&& leo x' y' y11)) )
  and gto y12 y13 y14 =
    fresh (zz) (y12 === succ zz &&& (y13 === zero &&& (y14 === !!true)))
    ||| (y12 === zero &&& (y14 === !!false) ||| fresh (y' x') (y12 === succ x' &&& (y13 === succ y' &&& gto x' y' y14)))
  in
  sorto x0 x1



open GT

let runTest msg sortFn lst =
   printf "%s: %!" msg;
   printf "%s\n%!" @@ (show(list) (show(int))) @@ sortGen sortFn lst 

let runTime msg sortFn lst  =
   printf "%s:%!" msg;
   let startT = Sys.time() in
   let resutl = sortGen sortFn lst in
   let endT = Sys.time() in
   printf "%f\n%!" (endT -. startT)

let test1 msg sort =
  runTest msg sort [4; 3; 2; 1];
  runTest msg sort [5; 4; 3; 2; 1];
  runTest msg sort [15; 14; 13; 12; 11; 10; 9; 8; 7; 6; 5; 4; 3; 2; 1]

let _ =
  test1 "Ori" sorto;
  test1 "Fu " fuluSort;
  test1 "Su " sequSort;
  test1 "MnU" maxuSort;
  test1 "MxU" minuSort;
  test1 "Ru " recuSort;
  test1 "Nu " nrcuSort
