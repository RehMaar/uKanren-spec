(*
Запрос: Path.query1.
*)


module L = List

open GT
open OCanren
open Std
open Nat

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

let topLevelMyFU x0 x1 =
  let rec isPath y0 y1 =
    fresh (q1 q2 q3 q4)
      ( y0 === nil ()
      ||| ( y0
          === q1 % nil ()
          ||| (y0 === q2 % (q3 % q4) &&& isPath (q3 % q4) y1 &&& (y0 === q2 % (q3 % q4) &&& elem q2 q3 y1)) )
      )
  and elem y2 y3 y4 =
    fresh (q1 q2 q3 q4 q5 q6)
      ( y4
      === pair q1 q2 % q3
      &&& eqNatEqNat y2 q1 y3 q2
      ||| ( y4 === q4 % q5 &&& elem y2 y3 q5
          &&& ((q4 === pair q2 q6)
              &&& _eqNatEqNat y2 q2 y3 q6
              ||| ((q4 === pair q2 q6) &&& __eqNatEqNat y2 q2 y3 q6) ) ) )
  and eqNatEqNat y5 y6 y7 y8 =
    fresh (q1 q2 q3 q4)
      ( y5 === zero &&& (y6 === zero) &&& (y7 === zero) &&& (y8 === zero)
      ||| ( y5 === zero &&& (y6 === zero)
          &&& (y7 === s q1)
          &&& (y8 === s q2)
          &&& eqNat q1 q2
          ||| ( y5 === s q3
              &&& (y6 === s q4)
              &&& (y7 === zero) &&& (y8 === zero) &&& eqNat q3 q4
              ||| (y5 === s q3 &&& (y6 === s q4) &&& (y7 === s q1) &&& (y8 === s q2) &&& eqNatEqNat q3 q4 q1 q2) ) ) )
  and eqNat y9 y10 = fresh (q1 q2) (y9 === zero &&& (y10 === zero) ||| (y9 === s q1 &&& (y10 === s q2) &&& eqNat q1 q2))
  and _eqNatEqNat y11 y12 y13 y14 =
    fresh (q1 q2 q3 q4 q5 q6 q7 q8)
      ( y11 === s q1 &&& (y12 === zero) &&& (y13 === zero) &&& (y14 === zero)
      ||| ( y11 === s q1 &&& (y12 === zero)
          &&& (y13 === s q2)
          &&& (y14 === zero)
          ||| ( y11 === s q1 &&& (y12 === zero) &&& (y13 === zero)
              &&& (y14 === s q3)
              ||| ( y11 === s q1 &&& (y12 === zero)
                  &&& (y13 === s q4)
                  &&& (y14 === s q5)
                  &&& _eqNat q4 q5
                  ||| ( y11 === zero
                      &&& (y12 === s q6)
                      &&& (y13 === zero) &&& (y14 === zero)
                      ||| ( y11 === zero
                          &&& (y12 === s q6)
                          &&& (y13 === s q2)
                          &&& (y14 === zero)
                          ||| ( y11 === zero
                              &&& (y12 === s q6)
                              &&& (y13 === zero)
                              &&& (y14 === s q3)
                              ||| ( y11 === zero
                                  &&& (y12 === s q6)
                                  &&& (y13 === s q4)
                                  &&& (y14 === s q5)
                                  &&& _eqNat q4 q5
                                  ||| ( y11 === s q7
                                      &&& (y12 === s q8)
                                      &&& (y13 === zero) &&& (y14 === zero) &&& __eqNat q7 q8
                                      ||| ( y11 === s q7
                                          &&& (y12 === s q8)
                                          &&& (y13 === s q2)
                                          &&& (y14 === zero) &&& __eqNat q7 q8
                                          ||| ( y11 === s q7
                                              &&& (y12 === s q8)
                                              &&& (y13 === zero)
                                              &&& (y14 === s q3)
                                              &&& __eqNat q7 q8
                                              ||| (y11 === s q7 &&& (y12 === s q8) &&& (y13 === s q4) &&& (y14 === s q5) &&& _eqNatEqNat q7 q8 q4 q5) ) ) ) )
                              ) ) ) ) ) ) )
  and _eqNat y16 y17 =
    fresh (q1 q2 q3 q4)
      ( y16 === zero &&& (y17 === zero)
      ||| (y16 === s q1 &&& (y17 === zero) ||| (y16 === zero &&& (y17 === s q2) ||| (y16 === s q3 &&& (y17 === s q4) &&& _eqNat q3 q4))) )
  and __eqNat y19 y20 =
    fresh (q1 q2 q3 q4) (y19 === s q1 &&& (y20 === zero) ||| (y19 === zero &&& (y20 === s q2) ||| (y19 === s q3 &&& (y20 === s q4) &&& __eqNat q3 q4)))
  and __eqNatEqNat y21 y22 y23 y24 =
    fresh (q1 q2 q3 q4 q5 q6)
      ( y21 === zero &&& (y22 === zero)
      &&& (y23 === s q1)
      &&& (y24 === zero)
      ||| ( y21 === zero &&& (y22 === zero) &&& (y23 === zero)
          &&& (y24 === s q2)
          ||| ( y21 === zero &&& (y22 === zero)
              &&& (y23 === s q3)
              &&& (y24 === s q4)
              &&& __eqNat q3 q4
              ||| ( y21 === s q5
                  &&& (y22 === s q6)
                  &&& (y23 === s q1)
                  &&& (y24 === zero) &&& eqNat q5 q6
                  ||| ( y21 === s q5
                      &&& (y22 === s q6)
                      &&& (y23 === zero)
                      &&& (y24 === s q2)
                      &&& eqNat q5 q6
                      ||| (y21 === s q5 &&& (y22 === s q6) &&& (y23 === s q3) &&& (y24 === s q4) &&& __eqNatEqNat q5 q6 q3 q4) ) ) ) ) )
  in
  isPath x0 x1

let topLevelMySUOrig x0 x1 =
  let rec isPath y0 y1 =
    fresh (q1 q2 q3 q4)
      ( y0 === nil ()
      ||| ( y0 === q1 % nil ()
      ||| (y0 === q2 % (q3 % q4) &&& isPath (q3 % q4) y1 &&& (y0 === q2 % (q3 % q4) &&& (!!true === !!true) &&& (!!true === !!true) &&& elem q2 q3 y1)) )
      )
  and elem y2 y3 y4 =
    fresh (q1 q2 q3 q4 q5 q6)
      ( y4
      === pair q1 q2 % q3
      &&& eqNatEqNat y2 q1 y3 q2
      ||| ( y4 === q4 % q5 &&& elem y2 y3 q5
          &&& ( y4 === q4 % q5 &&& (!!false === !!false)
              &&& (q4 === pair q2 q6)
              &&& _eqNatEqNat y2 q2 y3 q6
              ||| (y4 === q4 % q5 &&& (!!false === !!false) &&& (q4 === pair q2 q6) &&& __eqNatEqNat y2 q2 y3 q6) ) ) )
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
let topLevelMySU2 x0 x1 =
  let rec isPath y0 y1 =
    fresh (q1 q2 q3 q4 q5)
      ( y0 === nil ()
      ||| ( y0
          === q1 % nil ()
          ||| (y0 === q2 % (q3 % q4) &&& isPath q5 y1 &&& (y0 === q2 % (q3 % q4) &&& (!!true === !!true) &&& (!!true === !!true) &&& elem q2 q3 y1)) ) )
  and elem y2 y3 y4 =
    fresh (q1 q2 q3 q4 q5 q6)
      ( y4
      === pair q1 q2 % q3
      &&& eqNatEqNat y2 q1 y3 q2
      ||| ( y4 === q4 % q3 &&& elem y2 y3 q5
          &&& ( y4 === q4 % q3 &&& (!!false === !!false)
              &&& (q4 === pair q2 q6)
              &&& _eqNatEqNat y2 q2 y3 q6
              ||| (y4 === q4 % q3 &&& (!!false === !!false) &&& (q4 === pair q2 q6) &&& __eqNatEqNat y2 q2 y3 q6) ) ) )
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

let topLevelMySU x0 x1 =
  let rec isPath y0 y1 = fresh (q1 q2 q3 q4) (y0 === nil () ||| (y0 === q1 % nil () ||| (y0 === q2 % (q3 % q4) &&& (isPath (q3 % q4) y1 &&& elem q2 q3 y1))))
  and elem y2 y3 y4 =
    fresh (q1 q2 q3 q4 q5 q6)
      ( y4
      === pair q1 q2 % q3
      &&& eqNatEqNat y2 q1 y3 q2
      ||| (y4 === q4 % q5 &&& (elem y2 y3 q5 &&& (q4 === pair q2 q6 &&& _eqNatEqNat y2 q2 y3 q6 ||| (q4 === pair q2 q6 &&& __eqNatEqNat y2 q2 y3 q6)))) )
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

let topLevelSU3 x0 x1 =
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


let g10 = ocanren( [(1,2);(1,3);(1,4);(1,5);(1,6);(1,7);(1,8);(1,9);(1,10);(2,1);(2,3);(2,4);(2,5);(2,6);(2,7);(2,8);(2,9);(2,10);(3,1);(3,2);(3,4);(3,5);(3,6);(3,7);(3 ,8);(3,9);(3,10);(4,1);(4,2);(4,3);(4,5);(4,6);(4,7);(4,8);(4,9);(4,10);(5,1);(5,2);(5,3);(5,4);(5,6);(5,7);(5,8);(5,9);(5,10);(6,1);(6,2);(6,3);(6,4);(6,5);(6,7);(6,8);(6,9);(6,10);(7,1);(7,2);(7,3);(7,4);(7,5);(7,6);(7,8);(7,9);(7,10);(8,1);(8,2);(8,3);(8,4);(8,5);(8,6);(8,7);(8,9);(8,10);(9,1);(9,2);(9,3);(9,4);(9,5);(9,6);(9,7);(9,8);(9,10);(10,1);(10,2);(10,3);(10,4);(10,5);(10,6);(10,7);(10,8);(10,9)])
let g3 = ocanren([(1,2);(1,3);(2,1);(2,3);(3,1);(3,2)])
let g2 = ocanren([(1,2);(2,1)])
let gg = ocanren([(0, 1); (1, 2); (2, 0); (1, 3); (3, 0)])

let g = g10

(*let result_my_ru = run q (fun q -> topLevelMyRU q g) id*)

let test x = 
        let result_cpd = run q (fun q -> topLevelCPD q g) id in
        let result_my_su = run q (fun q -> topLevelSU3 q g) id in
        let result_my_fu = run q (fun q -> topLevelMyFU q g) id in
        let result_orig = run q (fun q -> isPath q g (!!true)) id in

        Printf.printf "> CPD:\n%!";
        let t1 = Sys.time() in
        let cpd = Stream.take ~n:x result_cpd in
        let t2 = Sys.time() in
        Printf.printf "CPD time: %fs\n%!" (t2 -. t1);
        Printf.printf "CPD Answers: %d\n%!" @@ L.length cpd;

        Printf.printf "> Rel:\n%!";
        let t1 = Sys.time() in
        let rel = Stream.take ~n:x result_orig in
        let t2 = Sys.time() in
        Printf.printf "My time: %fs\n%!" (t2 -. t1);
        Printf.printf "My Answers: %d\n%!" @@ L.length rel;

        Printf.printf "> SeqUnfold:\n%!";
        let t1 = Sys.time() in
        let su = Stream.take ~n:x result_my_su in
        let t2 = Sys.time() in
        Printf.printf "My time: %fs\n%!" (t2 -. t1);
        Printf.printf "My Answers: %d\n%!" @@ L.length su;

        Printf.printf "> FullUnfold:\n%!";
        let t1 = Sys.time() in
        let fu = Stream.take ~n:x result_my_fu in
        let t2 = Sys.time() in
        Printf.printf "My time: %fs\n%!" (t2 -. t1);
        Printf.printf "My Answers: %d\n%!" @@ L.length fu


let _ = Printf.printf "Test 100.\n%!";
        test 100;
        Printf.printf "Test 500.\n%!";
        test 500;
        Printf.printf "Test 1000.\n%!";
        test 1000;
