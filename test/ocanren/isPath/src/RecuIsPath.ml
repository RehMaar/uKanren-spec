open GT
open OCanren
open Std
open Nat

let recuIsPath x0 x1 =
  let rec isPath y0 y1 =
    fresh (x11 x5 x4 x3 x2) (y0 === nil () ||| (y0 === x2 % nil () ||| (y0 === x3 % (x4 % x5) &&& (x11 === x4 % x5 &&& isPath x11 y1 &&& elem x3 x4 y1))))
  and elem y2 y3 y4 =
    fresh (x50 x48 x47 x41 x22 x21 x15 x14)
      ( y4 === x14 % x15
      &&& (x14 === pair x21 x22 &&& eqNatEqNat y2 x21 y3 x22)
      ||| ( y4 === x14 % x41
          &&& (elem y2 y3 x41 &&& (x14 === pair x47 x48 &&& _eqNatEqNat y2 x47 y3 x48 x50 ||| (x14 === pair x47 x48 &&& __eqNatEqNat y2 x47 y3 x48))) ) )
  and eqNatEqNat y5 y6 y7 y8 =
    fresh (x30 x29) (y5 === zero &&& (y6 === zero) &&& eqNat y7 y8 ||| (y5 === s x29 &&& (y6 === s x30) &&& eqNatEqNat x29 x30 y7 y8))
  and eqNat y9 y10 = fresh (x36 x35) (y9 === zero &&& (y10 === zero) ||| (y9 === s x35 &&& (y10 === s x36) &&& eqNat x35 x36))
  and _eqNatEqNat y11 y12 y13 y14 y15 =
    fresh (x56 x55 x54 x53)
      ( y11 === s x53 &&& (y12 === zero) &&& _eqNat y13 y14 y15
      ||| (y11 === zero &&& (y12 === s x54) &&& _eqNat y13 y14 y15 ||| (y11 === s x55 &&& (y12 === s x56) &&& _eqNatEqNat x55 x56 y13 y14 y15)) )
  and _eqNat y16 y17 y18 =
    fresh (x62 x61 x60 x59)
      ( y16 === zero &&& (y17 === zero) &&& (y18 === !!true)
      ||| ( y16 === s x59 &&& (y17 === zero) &&& (y18 === !!false)
          ||| (y16 === zero &&& (y17 === s x60) &&& (y18 === !!false) ||| (y16 === s x61 &&& (y17 === s x62) &&& _eqNat x61 x62 y18)) ) )
  and __eqNatEqNat y19 y20 y21 y22 =
    fresh (x74 x73) (y19 === zero &&& (y20 === zero) &&& __eqNat y21 y22 ||| (y19 === s x73 &&& (y20 === s x74) &&& __eqNatEqNat x73 x74 y21 y22))
  and __eqNat y23 y24 =
    fresh (x80 x79 x78 x77)
      (y23 === s x77 &&& (y24 === zero) ||| (y23 === zero &&& (y24 === s x78) ||| (y23 === s x79 &&& (y24 === s x80) &&& __eqNat x79 x80)))
  in
  isPath x0 x1
