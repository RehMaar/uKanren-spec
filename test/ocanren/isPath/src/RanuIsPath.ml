open GT
open OCanren
open Std
open Nat

let ranuIsPath x0 x1 =
  let rec isPath y0 y1 =
    fresh (x11 x5 x4 x3 x2) (y0 === nil () ||| (y0 === x2 % nil () ||| (y0 === x3 % (x4 % x5) &&& (x11 === x4 % x5 &&& isPath x11 y1 &&& elem x3 x4 y1))))
  and elem y2 y3 y4 =
    fresh (x50 x48 x47 x41 x22 x21 x15 x14)
      ( y4 === x14 % x15
      &&& (x14 === pair x21 x22 &&& eqNatEqNat y2 x21 y3 x22)
      ||| ( y4 === x14 % x41
          &&& (elem y2 y3 x41 &&& (x14 === pair x47 x48 &&& _eqNatEqNat y2 x47 y3 x48 x50 ||| (x14 === pair x47 x48 &&& __eqNatEqNat y2 x47 y3 x48))) ) )
  and eqNatEqNat y5 y6 y7 y8 =
    fresh (x30 x29) (y7 === zero &&& (y8 === zero) &&& eqNat y5 y6 ||| (y7 === s x29 &&& (y8 === s x30) &&& eqNatEqNat y5 y6 x29 x30))
  and eqNat y9 y10 = fresh (x36 x35) (y9 === zero &&& (y10 === zero) ||| (y9 === s x35 &&& (y10 === s x36) &&& eqNat x35 x36))
  and _eqNatEqNat y11 y12 y13 y14 y15 =
    fresh (x56 x55 x54 x53)
      ( y13 === zero &&& (y14 === zero) &&& (y15 === !!true) &&& _eqNat y11 y12
      ||| ( y13 === s x53 &&& (y14 === zero) &&& (y15 === !!false) &&& _eqNat y11 y12
          ||| ( y13 === zero
              &&& (y14 === s x54)
              &&& (y15 === !!false) &&& _eqNat y11 y12
              ||| (y13 === s x55 &&& (y14 === s x56) &&& _eqNatEqNat y11 y12 x55 x56 y15) ) ) )
  and _eqNat y16 y17 =
    fresh (x62 x61 x60 x59) (y16 === s x59 &&& (y17 === zero) ||| (y16 === zero &&& (y17 === s x60) ||| (y16 === s x61 &&& (y17 === s x62) &&& _eqNat x61 x62)))
  and __eqNatEqNat y18 y19 y20 y21 =
    fresh (x74 x73 x72 x71)
      ( y20 === s x71 &&& (y21 === zero) &&& eqNat y18 y19
      ||| (y20 === zero &&& (y21 === s x72) &&& eqNat y18 y19 ||| (y20 === s x73 &&& (y21 === s x74) &&& __eqNatEqNat y18 y19 x73 x74)) )
  in
  isPath x0 x1
