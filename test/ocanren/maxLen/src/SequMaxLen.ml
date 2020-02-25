open GT
open OCanren
open Std
open Nat

let sequMaxLen x0 x1 x2 =
  let rec maxLengtho y0 y1 y2 =
    fresh (x17 x19 x18 x5)
      ( y0 === nil () &&& (y2 === zero) &&& (y1 === zero)
      ||| (y0 === x5 % x18 &&& (y2 === succ x19) &&& (x17 === x5 % x18 &&& maxo1 x17 y1 &&& (x17 === x5 % x18 &&& lengtho x18 x19))) )
  and maxo1 y3 y4 =
    fresh (x36 x25 x24 x22)
      (y3 === nil () &&& (y4 === zero) ||| (y3 === zero % x22 &&& maxo1 x22 y4 ||| (y3 === x24 % x25 &&& (x24 === succ x36 &&& _maxo1 x25 x36 y4))))
  and _maxo1 y5 y6 y7 =
    fresh (x67 x66 x43 x52 x48 x40)
      ( y5 === nil ()
      &&& (y7 === succ y6)
      ||| ( y5 === x40 % x48
          &&& (_maxo1 x48 y6 y7 &&& (x40 === zero ||| (x40 === succ x52 &&& leo x52 y6)))
          ||| (y5 === x43 % x66 &&& (x43 === succ x67 &&& (_maxo1 x66 x67 y7 &&& gto x67 y6))) ) )
  and leo y8 y9 = fresh (x58 x57) (y8 === zero ||| (y8 === succ x57 &&& (y9 === succ x58) &&& leo x57 x58))
  and gto y10 y11 = fresh (x72 x71 x70) (y10 === succ x70 &&& (y11 === zero) ||| (y10 === succ x71 &&& (y11 === succ x72) &&& gto x71 x72))
  and lengtho y12 y13 = fresh (x78 x77 x76) (y12 === nil () &&& (y13 === zero) ||| (y12 === x76 % x77 &&& (y13 === succ x78) &&& lengtho x77 x78)) in
  maxLengtho x0 x1 x2
