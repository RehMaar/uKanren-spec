open GT
open OCanren
open Std
open Nat

let ranuMaxLen x0 x1 x2 =
  let rec maxLengtho y0 y1 y2 =
    fresh (x17 x19 x18 x4)
      ( y0 === nil () &&& (y2 === zero) &&& (y1 === zero)
      ||| (y0 === x4 % x18 &&& (y2 === succ x19) &&& (x17 === x4 % x18 &&& maxo1 x17 y1 &&& (x17 === x4 % x18 &&& lengtho x18 x19))) )
  and maxo1 y3 y4 =
    fresh (x26 x25 x23) (y3 === nil () &&& (y4 === zero) ||| (y3 === zero % x23 &&& maxo1 x23 y4 ||| (y3 === x25 % x26 &&& gtoMaxo1 x25 x26 y4)))
  and gtoMaxo1 y5 y6 y7 =
    fresh (x58 x59 x49 x37)
      ( y6 === nil () &&& (y7 === y5) &&& gto y5
      ||| (y6 === x37 % x49 &&& (gtoMaxo1 y5 x49 y7 &&& leo x37 y5) ||| (y6 === x59 % x58 &&& (gto y5 &&& (_maxo1 x58 x59 y7 &&& _gto x59 y5)))) )
  and gto y8 = fresh (x44) (y8 === succ x44)
  and leo y9 y10 = fresh (x54 x53) (y9 === zero ||| (y9 === succ x53 &&& (y10 === succ x54) &&& leo x53 x54))
  and _maxo1 y11 y12 y13 =
    fresh (x74 x75 x70 x62)
      ( y11 === nil () &&& (y13 === y12)
      ||| (y11 === x62 % x70 &&& (_maxo1 x70 y12 y13 &&& leo x62 y12) ||| (y11 === x75 % x74 &&& (_maxo1 x74 x75 y13 &&& _gto x75 y12))) )
  and _gto y14 y15 = fresh (x80 x79 x78) (y14 === succ x78 &&& (y15 === zero) ||| (y14 === succ x79 &&& (y15 === succ x80) &&& _gto x79 x80))
  and lengtho y16 y17 = fresh (x87 x86 x85) (y16 === nil () &&& (y17 === zero) ||| (y16 === x85 % x86 &&& (y17 === succ x87) &&& lengtho x86 x87)) in
  maxLengtho x0 x1 x2