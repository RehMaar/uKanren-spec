open GT
open OCanren
open OCanren.Std
open Nat

let cpdIsPath x0 x1 =
  let rec isPath y0 y1 = fresh (q1 q2 q3 q4) (y0 === nil () ||| (y0 === q1 % nil ()) ||| (y0 === q2 % (q3 % q4) &&& (elem y1 q2 q3 &&& isPath (q3 % q4) y1)))
  and elem y2 y3 y4 =
    fresh (q1 q2 q3 q4)
      (y2 === pair q1 q2 % q3 &&& (__eqNat y3 q1 !!true &&& __eqNat y4 q2 !!true) ||| (y2 === q4 % q3 &&& (eqPair y3 y4 q4 &&& elem q3 y3 y4)))
  and eqPair y9 y10 y11 =
    fresh (q1 q2 q3)
      (y11 === pair q1 q2 &&& (__eqNat y9 q1 !!false &&& __eqNat y10 q2 q3) ||| (y11 === pair q1 q2 &&& (__eqNat y9 q1 !!true &&& __eqNat y10 q2 !!false)))
  and __eqNat y12 y13 y14 =
    fresh (q1 q2 q3 q4)
      ( y12 === zero
      &&& (y13 === zero)
      &&& (y14 === !!true)
      ||| (y12 === s q1 &&& (y13 === zero) &&& (y14 === !!false))
      ||| (y12 === zero &&& (y13 === s q2) &&& (y14 === !!false))
      ||| (y12 === s q3 &&& (y13 === s q4) &&& __eqNat q3 q4 y14) )
  in
  isPath x0 x1
