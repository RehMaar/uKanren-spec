(*
Запрос: Path.query1.
*)

module L = List

open GT
open OCanren
open Std
open Nat

open FuluIsPath
open MaxuIsPath
open MinuIsPath
open NrcuIsPath
open RanuIsPath
open RecuIsPath
open SequIsPath
open FstuIsPath
open CpdIsPath2

let rec eqNat a b q23 =
  fresh (q24) (q24 === (pair a b))
    (conde
       [(q24 === (pair (zero) (zero))) &&& (q23 === (!! true));
       fresh (q26) (q24 === (pair (s q26) (zero))) (q23 === (!! false));
       fresh (q28) (q24 === (pair (zero) (s q28))) (q23 === (!! false));
       fresh (x y) (q24 === (pair (s x) (s y))) (eqNat x y q23)])

let eqPair a b q14 =
  fresh (q15 a1 a2 b1 b2 q16 q17) (q15 === (pair a b)) (q15 === (pair (pair a1 a2) (pair b1 b2))) (
    eqNat a1 b1 q16) (eqNat a2 b2 q17) (conde [(q16 === (!! false)) &&& (q14 === (!! false)); (q16 === (!! true)) &&& (q14 === q17)])

let rec elem x g q9 =
  ((g === (nil ())) &&& (q9 === (!! false))) |||
    (fresh (y ys q12) (g === (y % ys)) (eqPair x y q12) (conde [(q12 === (!! true)) &&& (q9 === (!! true)); (q12 === (!! false)) &&& (elem x ys q9)]))

let rec isPath c g q0 =
  (fresh (q1) (c === (q1 % (nil ()))) (q0 === (!! true))) |||
    (fresh (x1 x2 xs q3 q4) (c === (x1 % (x2 % xs))) (elem (pair x1 x2) g q3) (
       isPath (x2 % xs) g q4) (conde [(q3 === (!! false)) &&& (q0 === (!! false)); (q3 === (!! true)) &&& (q0 === q4)]))

let rec lengtho y14 y15 = y14 === nil () &&& (y15 === zero) ||| fresh (z t h) (y14 === h % t &&& (y15 === succ z &&& lengtho t z))

let k10 = ocanren([(1,2);(1,3);(1,4);(1,5);(1,6);(1,7);(1,8);(1,9);(1,10);(2,1);(2,3);(2,4);(2,5);(2,6);(2,7);(2,8);(2,9);(2,10);(3,1);(3,2);(3,4);(3,5);(3,6);(3,7);(3 ,8);(3,9);(3,10);(4,1);(4,2);(4,3);(4,5);(4,6);(4,7);(4,8);(4,9);(4,10);(5,1);(5,2);(5,3);(5,4);(5,6);(5,7);(5,8);(5,9);(5,10);(6,1);(6,2);(6,3);(6,4);(6,5);(6,7);(6,8);(6,9);(6,10);(7,1);(7,2);(7,3);(7,4);(7,5);(7,6);(7,8);(7,9);(7,10);(8,1);(8,2);(8,3);(8,4);(8,5);(8,6);(8,7);(8,9);(8,10);(9,1);(9,2);(9,3);(9,4);(9,5);(9,6);(9,7);(9,8);(9,10);(10,1);(10,2);(10,3);(10,4);(10,5);(10,6);(10,7);(10,8);(10,9)])
let g3 = ocanren([(1,2);(1,3);(2,1);(2,3);(3,1);(3,2)])
let g2 = ocanren([(1,2);(2,1)])
let gg = ocanren([(0, 1); (1, 2); (2, 0); (1, 3); (3, 0)])

let gHam = ocanren([(1, 2); (2, 1); (2, 3); (3, 2); (3, 4); (4, 3); (4, 5); (5, 4); (5, 1); (1, 5);
                    (1, 6); (6, 1); (2, 7); (7, 2); (3, 8); (8, 3); (4, 9); (9, 4); (5, 10); (10, 5);
                    (6, 12); (12, 6); (12, 7); (7, 12); (7, 13); (13, 7); (13, 8); (8, 13); (8, 14); (14, 8);
                    (14, 9); (9, 14); (9, 15); (15, 9); (15, 10); (10, 15); (10, 11); (11, 10); (11, 6); (6, 11);
                    (12, 17); (17, 12); (13, 18); (18, 13); (14, 19); (19, 14); (15, 20); (20, 15); (11, 16); (16, 11);
                    (17, 18); (18, 17); (18, 19); (19, 18); (19, 20); (20, 19); (20, 16); (16, 20); (16, 17); (17, 16)])

let loop = ocanren([(1, 1)])
let dag = ocanren([(1, 2); (2, 3)])
let gr = ocanren([(1, 2); (2, 3); (3, 1)])

let g = k10

let testOn name x result = 
        (*Printf.printf "> %s:\n%!" name;*)
        let t1 = Sys.time() in
        let lst = Stream.take ~n:x result in
        let t2 = Sys.time() in
        Printf.printf "%s: %fs\n%!" name (t2 -. t1);
(*        Printf.printf "%s Answers: %d\n%!" name @@ L.length lst;
        L.iter (fun c -> Printf.printf "g: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify)) lst;*)
        ()

let testLen x y = 
  testOn "Orig" x (run q (fun q -> lengtho q y &&& isPath q g !!true) id);
  testOn "CPD " x (run q (fun q -> lengtho q y &&& cpdIsPath2 q g) id);
  testOn "FU  " x (run q (fun q -> lengtho q y &&& fuluIsPath q g) id);
  testOn "SU  " x (run q (fun q -> lengtho q y &&& sequIsPath q g) id);
  testOn "MaxU" x (run q (fun q -> lengtho q y &&& maxuIsPath q g) id);
  testOn "MinU" x (run q (fun q -> lengtho q y &&& minuIsPath q g) id);
  testOn "RecU" x (run q (fun q -> lengtho q y &&& recuIsPath q g) id);
  testOn "NrcU" x (run q (fun q -> lengtho q y &&& nrcuIsPath q g) id);
  testOn "FstU " x (run q (fun q -> lengtho q y &&& fstuIsPath q g) id);
  Printf.printf "%!"

let test x = 
  testOn "Orig" x (run q (fun q -> isPath q g !!true) id);
  testOn "CPD " x (run q (fun q -> cpdIsPath2 q g) id);
  testOn "FU  " x (run q (fun q -> fuluIsPath q g) id);
  testOn "FstU " x (run q (fun q -> fstuIsPath q g) id);
  testOn "SU  " x (run q (fun q -> sequIsPath q g) id);
  testOn "MaxU" x (run q (fun q -> maxuIsPath q g) id);
  testOn "MinU" x (run q (fun q -> minuIsPath q g) id);
  testOn "RecU" x (run q (fun q -> recuIsPath q g) id);
  testOn "NrcU" x (run q (fun q -> nrcuIsPath q g) id);
  Printf.printf "%!"

(*
let runTest = 
  Printf.printf "Test 100.\n%!";
  test 100;
  Printf.printf "Test 500.\n%!";
  test 500;
  Printf.printf "Test 1000.\n%!";
  test 1000;
  ()*)

let _ = 
(*
   Printf.printf "#Len 5\n%!";
   testLen 1 (ocanren(5));
   Printf.printf "#Len 7\n%!";
   testLen 1 (ocanren(7));*)
   Printf.printf "#Len 9\n%!";
   testLen 1 (ocanren(9));
   Printf.printf "#Len 11\n%!";
   testLen 1 (ocanren(11));
   Printf.printf "#Len 13\n%!";
   testLen 1 (ocanren(13));
   Printf.printf "#Len 15\n%!";
   testLen 1 (ocanren(15));
   ()
