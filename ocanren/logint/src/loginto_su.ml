open GT
open OCanren
open Std
open Nat

let topLevelSU x0 x1 x2 =
  let rec loginto y0 y1 y2 =
    fresh (q1 q2 q3 q4 q5 q6 q7 q8 q9 q10)
      ( y1 === lit y2
      ||| ( lookupo y0 y2
      ||| ( y1 === neg q1
          &&& (loginto y0 q1 q2 &&& (q2 === !!true &&& (y2 === !!false) ||| (y2 === !!true)))
      ||| ( y1 === conj q3 q4
          &&& (loginto y0 q3 q5 &&& (loginto y0 q4 q6 &&& (q5 === !!true &&& (q6 === !!true) &&& (y2 === !!true) ||| (y2 === !!false))))
      ||| ( y1 === disj q7 q8
          &&& ( loginto y0 q7 q9
          &&& (loginto y0 q8 q10 &&& (q9 === !!true &&& (y2 === !!true) ||| (q10 === !!true &&& (y2 === !!true) ||| (y2 === !!false)))))))
          ) ) )
  and lookupo y3 y5 = fresh (q1 q2 q3 q4) (y3 === pair q1 y5 % q2 ||| (y3 === pair q3 q4 % q2 &&& lookupo q2 y5)) in
  loginto x0 x1 x2
