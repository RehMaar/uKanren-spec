let topLevelCPD x0 x1 x2 =
  let rec maxLengtho y0 y1 y2 =
    fresh (q1 q2 q3 q4)
      ( y0 === nil () &&& (y1 === zero) &&& (y2 === zero)
      ||| (y0 === zero % q1 &&& (y2 === succ q2) &&& maxo1Lengtho y1 q1 q2)
      ||| (y0 === succ q3 % q4 &&& (y2 === succ q2) &&& _maxo1Lengtho y1 q3 q4 q2) )
  and maxo1Lengtho y3 y4 y5 =
    fresh (q1 q2 q3 q4)
      ( y4 === nil () &&& (y3 === zero) &&& (y5 === zero)
      ||| (y4 === zero % q1 &&& (y5 === succ q2) &&& maxo1Lengtho y3 q1 q2)
      ||| (y4 === succ q3 % q4 &&& (y5 === succ q2) &&& _maxo1Lengtho y3 q3 q4 q2) )
  and _maxo1Lengtho y6 y7 y8 y9 =
    fresh (q1 q2 q3 q4 q5 q6)
      ( y8 === nil () &&& (y6 === succ y7) &&& (y9 === zero)
      ||| (y8 === q1 % q2 &&& (y9 === succ q3) &&& (_maxo1Lengtho y6 y7 q2 q3 &&& _leo q1 (succ y7)))
      ||| (y8 === succ q4 % q5 &&& (y9 === succ q6) &&& (_maxo1Lengtho y6 q4 q5 q6 &&& gto q4 y7)) )
  and leo = fresh (q1 q2) (_leo q1 q2)
  and _leo y12 y13 = fresh (q1 q2) (y12 === zero ||| (y12 === succ q1 &&& (y13 === succ q2) &&& _leo q1 q2))
  and gto y14 y15 = fresh (q1 q2 q3) (y14 === succ q1 &&& (y15 === zero) ||| (y14 === succ q2 &&& (y15 === succ q3) &&& gto q2 q3)) in
  maxLengtho x0 x1 x2
