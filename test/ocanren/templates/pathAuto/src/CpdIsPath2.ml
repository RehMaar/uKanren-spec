open GT
open OCanren
open OCanren.Std
open Nat

let cpdIsPath2 x0 x1 =
  let rec isPath y0 y1 = fresh (x5 x4 x3 x2) (y0 === nil () ||| (y0 === x2 % nil ()) ||| (y0 === x3 % (x4 % x5) &&& (elem y1 x3 x4 &&& isPath (x4 % x5) y1)))
  and elem y2 y3 y4 =
    fresh (x16 x15 x10 x9)
      ( y2 === x9 % x10
      &&& (x9 === pair x15 x16)
      &&& (__eqNat y3 x15 !!true &&& __eqNat y4 x16 !!true)
      ||| (y2 === x9 % x10 &&& (eqPair y3 y4 x9 &&& elem x10 y3 y4)) )
  and eqNat y5 y6 = fresh (x23 x22) (y5 === zero &&& (y6 === zero) ||| (y5 === s x22 &&& (y6 === s x23) &&& __eqNat x22 x23 !!true))
  and _eqNat y7 y8 = fresh (x23 x22) (y7 === zero &&& (y8 === zero) ||| (y7 === s x22 &&& (y8 === s x23) &&& __eqNat x22 x23 !!true))
  and eqPair y9 y10 y11 =
    fresh (x18 x16 x15)
      ( y11 === pair x15 x16
      &&& (__eqNat y9 x15 !!false &&& __eqNat y10 x16 x18)
      ||| (y11 === pair x15 x16 &&& (__eqNat y9 x15 !!true &&& __eqNat y10 x16 !!false)) )
  and __eqNat y12 y13 y14 =
    fresh (x23 x22 x21 x20)
      ( y12 === zero
      &&& (y13 === zero)
      &&& (y14 === !!true)
      ||| (y12 === s x20 &&& (y13 === zero) &&& (y14 === !!false))
      ||| (y12 === zero &&& (y13 === s x21) &&& (y14 === !!false))
      ||| (y12 === s x22 &&& (y13 === s x23) &&& __eqNat x22 x23 y14) )
  in
  isPath x0 x1
