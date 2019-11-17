open GT
open OCanren
open Std
open Nat

let topLevelSU x0 x1 x2 =
  let rec maxLengtho y0 y1 y2 =
    fresh (q1 q2 q3) (y0 === nil () &&& (y2 === zero) &&& (y1 === zero) ||| (y0 === q1 % q2 &&& (y2 === succ q3) &&& (maxo1 (q1 % q2) y1 &&& lengtho q2 q3)))
  and maxo1 y3 y4 = fresh (q1 q2 q3 q4) (y3 === nil () &&& (y4 === zero) ||| (y3 === zero % q1 &&& maxo1 q1 y4 ||| (y3 === q2 % q3 &&& _maxo1 q3 q4 y4)))
  and _maxo1 y5 y6 y7 =
    fresh (q1 q2 q3 q4)
      ( y5 === nil ()
      &&& (y7 === succ y6)
      ||| (y5 === q1 % q2 &&& (_maxo1 q2 y6 y7 &&& (q1 === zero ||| leo)) ||| (y5 === succ q3 % q4 &&& (_maxo1 q4 q3 y7 &&& gto q3 y6))) )
  and gto y10 y11 = fresh (q1 q2 q3) (y10 === succ q1 &&& (y11 === zero) ||| (y10 === succ q2 &&& (y11 === succ q3) &&& gto q2 q3))
  and lengtho y12 y13 = fresh (q1 q2 q3) (y12 === nil () &&& (y13 === zero) ||| (y12 === q1 % q2 &&& (y13 === succ q3) &&& lengtho q2 q3)) in
  maxLengtho x0 x1 x2
