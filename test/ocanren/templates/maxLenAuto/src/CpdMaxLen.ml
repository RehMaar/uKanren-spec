open GT
open OCanren
open OCanren.Std
open Nat

let cpdMaxLen x0 x1 x2 =
  let rec maxLengtho y0 y1 y2 =
    fresh (x9 x7 x6 x4)
      ( y0 === nil () &&& (y1 === zero)
      &&& __lengtho (nil ()) y2
      ||| (y0 === zero % x4 &&& maxo1Lengtho y1 y2 x4)
      ||| (y0 === x6 % x7 &&& (x6 === succ x9) &&& ____maxo1Lengtho y1 y2 x9 x7 x7) )
  and lengtho y3 = y3 === zero
  and maxo1Lengtho y4 y5 y6 =
    fresh (x18 x16 x15 x13)
      ( y6 === nil () &&& (y4 === zero)
      &&& __lengtho (zero % nil ()) y5
      ||| (y6 === zero % x13 &&& (maxo1 y4 x13 &&& __lengtho (zero % (zero % x13)) y5))
      ||| (y6 === x15 % x16 &&& (x15 === succ x18) &&& __maxo1Lengtho y4 y5 x18 x16 x16) )
  and maxo1 y7 y8 =
    fresh (x29 x27 x26 x24)
      (y8 === nil () &&& (y7 === zero) ||| (y8 === zero % x24 &&& maxo1 y7 x24) ||| (y8 === x26 % x27 &&& (x26 === succ x29) &&& _maxo1 y7 x27 x29))
  and _maxo1 y9 y10 y11 =
    fresh (x39 x36 x35 x33 x32)
      ( y10 === nil ()
      &&& (y9 === succ y11)
      ||| (y10 === x32 % x33 &&& (_leo x32 (succ y11) &&& _maxo1 y9 x33 y11))
      ||| (y10 === x35 % x36 &&& (x35 === succ x39) &&& (gto x39 y11 &&& _maxo1 y9 x36 x39)) )
  and leo y12 y13 = fresh (x39) (y13 === zero ||| (y13 === succ x39 &&& _leo x39 y12))
  and _leo y14 y15 = fresh (x43 x42) (y14 === zero ||| (y14 === succ x42 &&& (y15 === succ x43) &&& _leo x42 x43))
  and gto y16 y17 = fresh (x43 x42 x41) (y16 === succ x41 &&& (y17 === zero) ||| (y16 === succ x42 &&& (y17 === succ x43) &&& gto x42 x43))
  and _lengtho y18 y19 =
    fresh (x28 x27 x26 x25) (y18 === succ zero &&& (y19 === nil ()) ||| (y18 === succ x25 &&& (y19 === x26 % x27) &&& (x25 === succ x28) &&& __lengtho x27 x28))
  and __lengtho y20 y21 = fresh (x31 x30 x29) (y20 === nil () &&& (y21 === zero) ||| (y20 === x29 % x30 &&& (y21 === succ x31) &&& __lengtho x30 x31))
  and _maxo1Lengtho y22 y23 y24 y25 =
    fresh (x28 x25 x24 x22 x21)
      ( y24 === nil ()
      &&& (y22 === succ y25)
      &&& __lengtho (zero % (succ y25 % nil ())) y23
      ||| (y24 === x21 % x22 &&& (__maxo1Lengtho y22 y23 y25 x22 (x21 % x22) &&& _leo x21 (succ y25)))
      ||| (y24 === x24 % x25 &&& (x24 === succ x28) &&& (gto x28 y25 &&& _maxo1 y22 x25 x28 &&& __lengtho (zero % (succ y25 % (succ x28 % x25))) y23)) )
  and __maxo1Lengtho y26 y27 y28 y29 y30 =
    fresh (x36 x33 x32 x30 x29)
      ( y29 === nil ()
      &&& (y26 === succ y28)
      &&& __lengtho (zero % (succ y28 % y30)) y27
      ||| (y29 === x29 % x30 &&& (__maxo1Lengtho y26 y27 y28 x30 y30 &&& _leo x29 (succ y28)))
      ||| (y29 === x32 % x33 &&& (x32 === succ x36) &&& (gto x36 y28 &&& _maxo1 y26 x33 x36 &&& __lengtho (zero % (succ y28 % y30)) y27)) )
  and ___maxo1Lengtho y31 y32 y33 y34 =
    fresh (x19 x16 x15 x13 x12)
      ( y33 === nil ()
      &&& (y31 === succ y34)
      &&& __lengtho (succ y34 % nil ()) y32
      ||| (y33 === x12 % x13 &&& (____maxo1Lengtho y31 y32 y34 x13 (x12 % x13) &&& _leo x12 (succ y34)))
      ||| (y33 === x15 % x16 &&& (x15 === succ x19) &&& (gto x19 y34 &&& _maxo1 y31 x16 x19 &&& __lengtho (succ y34 % (succ x19 % x16)) y32)) )
  and ____maxo1Lengtho y35 y36 y37 y38 y39 =
    fresh (x27 x24 x23 x21 x20)
      ( y38 === nil ()
      &&& (y35 === succ y37)
      &&& __lengtho (succ y37 % y39) y36
      ||| (y38 === x20 % x21 &&& (____maxo1Lengtho y35 y36 y37 x21 y39 &&& _leo x20 (succ y37)))
      ||| (y38 === x23 % x24 &&& (x23 === succ x27) &&& (gto x27 y37 &&& _maxo1 y35 x24 x27 &&& __lengtho (succ y37 % y39) y36)) )
  in
  maxLengtho x0 x1 x2

let cpdMaxLenOld x0 x1 x2 =
  let rec maxLengtho y0 y1 y2 =
    fresh (x9 x7 x6 x14 x4)
      ( y0 === nil () &&& (y1 === zero) &&& (y2 === zero)
      ||| (y0 === zero % x4 &&& (y2 === succ x14) &&& maxo1Lengtho y1 x4 x14)
      ||| (y0 === x6 % x7 &&& (x6 === succ x9) &&& (y2 === succ x14) &&& _maxo1Lengtho y1 x9 x7 x14) )
  and maxo1Lengtho y3 y4 y5 =
    fresh (x21 x19 x18 x26 x16)
      ( y4 === nil () &&& (y3 === zero) &&& (y5 === zero)
      ||| (y4 === zero % x16 &&& (y5 === succ x26) &&& maxo1Lengtho y3 x16 x26)
      ||| (y4 === x18 % x19 &&& (x18 === succ x21) &&& (y5 === succ x26) &&& _maxo1Lengtho y3 x21 x19 x26) )
  and _maxo1Lengtho y6 y7 y8 y9 =
    fresh (x26 x22 x19 x18 x23 x16 x15)
      ( y8 === nil ()
      &&& (y6 === succ y7)
      &&& (y9 === zero)
      ||| (y8 === x15 % x16 &&& (y9 === succ x23) &&& leoMaxo1Lengtho y6 y7 x15 x16 x23)
      ||| (y8 === x18 % x19 &&& (x18 === succ x22) &&& (y9 === succ x26) &&& gtoMaxo1Lengtho y6 x22 y7 x19 x26) )
  and leoMaxo1Lengtho y10 y11 y12 y13 y14 =
    fresh (x25) (y12 === zero &&& _maxo1Lengtho y10 y11 y13 y14 ||| (y12 === succ x25 &&& (_maxo1Lengtho y10 y11 y13 y14 &&& leo x25 y11)))
  and leo y15 y16 = fresh (x33 x32) (y15 === zero ||| (y15 === succ x32 &&& (y16 === succ x33) &&& leo x32 x33))
  and gtoMaxo1Lengtho y17 y18 y19 y20 y21 =
    fresh (x29 x28 x27)
      ( y18 === succ x27 &&& (y19 === zero)
      &&& _maxo1Lengtho y17 (succ x27) y20 y21
      ||| (y18 === succ x28 &&& (y19 === succ x29) &&& (_maxo1Lengtho y17 (succ x28) y20 y21 &&& gto x28 x29)) )
  and gto y22 y23 = fresh (x36 x35 x34) (y22 === succ x34 &&& (y23 === zero) ||| (y22 === succ x35 &&& (y23 === succ x36) &&& gto x35 x36)) in
  maxLengtho x0 x1 x2
