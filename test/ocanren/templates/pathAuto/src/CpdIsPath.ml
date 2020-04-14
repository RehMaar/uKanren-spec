open GT
open OCanren
open Std
open Nat

let cpdIsPath x0 x1 =
  let rec isPath y0 y1 = fresh (x5 x4 x3 x2) (y0 === nil () ||| (y0 === x2 % nil ()) ||| (y0 === x3 % (x4 % x5) &&& elemIsPath y1 x3 x4 x5))
  and elemIsPath y2 y3 y4 y5 =
    fresh (x15 x14 x9 x8)
      ( y2 === x8 % x9
      &&& (x8 === pair x14 x15)
      &&& (___eqNat y3 x14 !!true &&& ___eqNat y4 x15 !!true &&& isPath (y4 % y5) (pair x14 x15 % x9))
      ||| (y2 === x8 % x9 &&& (eqPairElem y3 y4 x8 x9 &&& isPath (y4 % y5) (x8 % x9))) )
  and eqNat y6 y7 = fresh (x24 x23) (y6 === zero &&& (y7 === zero) ||| (y6 === s x23 &&& (y7 === s x24) &&& ___eqNat x23 x24 !!true))
  and _eqNat y8 y9 = fresh (x24 x23) (y8 === zero &&& (y9 === zero) ||| (y8 === s x23 &&& (y9 === s x24) &&& ___eqNat x23 x24 !!true))
  and eqPairElem y10 y11 y12 y13 =
    fresh (x19 x17 x16)
      ( y12 === pair x16 x17
      &&& (eqNatElem y13 y10 y11 x16 &&& ___eqNat y11 x17 x19)
      ||| (y12 === pair x16 x17 &&& (__eqNatElem y13 y10 y11 x16 &&& _____eqNat y11 x17)) )
  and eqNatElem y14 y15 y16 y17 =
    fresh (x24 x23 x22 x21)
      ( y15 === s x21 &&& (y17 === zero)
      &&& _______elem y14 y16 (s x21)
      ||| (y15 === zero &&& (y17 === s x22) &&& _______elem y14 y16 zero)
      ||| (y15 === s x23 &&& (y17 === s x24) &&& _eqNatElem y14 y16 x23 x24) )
  and elem y18 y19 y20 =
    fresh (x39 x32 x31 x26 x25)
      ( y18 === x25 % x26
      &&& (x25 === pair x31 x32)
      &&& (x31 === s x39)
      &&& (___eqNat y20 x39 !!true &&& ___eqNat y19 x32 !!true)
      ||| (y18 === x25 % x26 &&& eqPairElem (s y20) y19 x25 x26) )
  and _eqNatElem y26 y27 y28 y29 =
    fresh (x29 x28 x27 x26)
      ( y28 === s x26 &&& (y29 === zero)
      &&& _______elem y26 y27 (s (s x26))
      ||| (y28 === zero &&& (y29 === s x27) &&& _______elem y26 y27 (s zero))
      ||| (y28 === s x28 &&& (y29 === s x29) &&& (_____eqNat x28 x29 &&& _______elem y26 y27 (s (s x28)))) )
  and __elem y30 y31 y32 =
    fresh (x49 x44 x37 x36 x31 x30)
      ( y30 === x30 % x31
      &&& (x30 === pair x36 x37)
      &&& (x36 === s x44)
      &&& (x44 === s x49)
      &&& (___eqNat y32 x49 !!true &&& ___eqNat y31 x37 !!true)
      ||| (y30 === x30 % x31 &&& eqPairElem (s (s y32)) y31 x30 x31) )
  and ___eqNat y42 y43 y44 =
    fresh (x24 x23 x22 x21)
      ( y42 === zero &&& (y43 === zero) &&& (y44 === !!true)
      ||| (y42 === s x21 &&& (y43 === zero) &&& (y44 === !!false))
      ||| (y42 === zero &&& (y43 === s x22) &&& (y44 === !!false))
      ||| (y42 === s x23 &&& (y43 === s x24) &&& ___eqNat x23 x24 y44) )
  and __eqNatElem y45 y46 y47 y48 =
    fresh (x24 x23) (y46 === zero &&& (y48 === zero) &&& _______elem y45 y47 zero ||| (y46 === s x23 &&& (y48 === s x24) &&& ___eqNatElem y45 y47 x23 x24))
  and ___eqNatElem y54 y55 y56 y57 =
    fresh (x29 x28)
      ( y56 === zero &&& (y57 === zero)
      &&& _______elem y54 y55 (s zero)
      ||| (y56 === s x28 &&& (y57 === s x29) &&& (___eqNat x28 x29 !!true &&& _______elem y54 y55 (s (s x28)))) )
  and _______elem y64 y65 y66 =
    fresh (x40 x39 x34 x33)
      ( y64 === x33 % x34
      &&& (x33 === pair x39 x40)
      &&& (___eqNat y66 x39 !!true &&& ___eqNat y65 x40 !!true)
      ||| (y64 === x33 % x34 &&& eqPairElem y66 y65 x33 x34) )
  and _____eqNat y67 y68 =
    fresh (x24 x23 x22 x21)
      (y67 === s x21 &&& (y68 === zero) ||| (y67 === zero &&& (y68 === s x22)) ||| (y67 === s x23 &&& (y68 === s x24) &&& _____eqNat x23 x24))
  in
  isPath x0 x1
