module L = List

open GT
open OCanren
open Std
open Nat

open MaxuPldrm
open MinuPldrm
open NrcuPldrm
open RecuPldrm
open SequPldrm
open FuluPldrm

let pldrmGen fn =
  List.to_list Nat.to_int @@
    RStream.hd @@
      run q (fun q -> fn q)
            (fun rr -> rr#prj)

let runTimeTest msg stream = 
   let t1 = Sys.time() in
   let x = RStream.take stream in
   let t2 = Sys.time() in
   let time = t2 -. t1 in
   Printf.printf "%s: %f\n%!" msg time

let runTest msg fn =
   Printf.printf "%s: %!" msg;
   Printf.printf "%s\n%!" @@ (show(list) (show(int))) @@ pldrmGen fn


let runT topLevel = run q (fun q -> topLevel q) (fun c -> c)

let x1 = ocanren([1; 2; 3; 4; 3; 2; 1])

let runTests =
  (*runTest "Orig" @@ run origPldrm x11 x12 x13;*)
  (*runTest "CPD " @@ run cpdPldrm x11 x12 x13;*)
  runTest "SU  " sequPldrm;
  runTest "NU  " nrcuPldrm;
  runTest "RU  " recuPldrm;
  runTest "MxU " maxuPldrm;
  runTest "MnU " minuPldrm;
  runTest "FU  " fuluPldrm

(*let runTimeTests =
  runTimeTest "Orig" @@ run origPldrm x21 x22 x23;
  runTimeTest "CPD " @@ run cpdPldrm  x21 x22 x23;
  runTimeTest "SU  " @@ run sequPldrm x21 x22 x23;
  runTimeTest "NU  " @@ run nrcuPldrm x21 x22 x23;
  runTimeTest "RU  " @@ run recuPldrm x21 x22 x23;
  runTimeTest "MxU " @@ run maxuPldrm x21 x22 x23;
  runTimeTest "MnU " @@ run minuPldrm x21 x22 x23;
  runTimeTest "FU  " @@ run fuluPldrm x21 x22 x23*)

let _ =
  runTests
(*  runTimeTests *)
