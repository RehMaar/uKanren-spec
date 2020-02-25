open GT
open OCanren
open Std
open Nat

open LogicExpr

let recuLogintS x0 =
  let rec loginto y0 =
    fresh (x53 x52 x27 x26 x9 x10 x28 x16)
      ( y0
      === pair (x ()) x16 % x28
      &&& lookupoNotoOro x28 x10 x16 x9
      ||| (y0 === pair x26 x27 % x52 &&& (x53 === pair x26 x27 % x52 &&& _lookupoNotoOro x52 x16 x9 x10 &&& (x53 === pair x26 x27 % x52 &&& lookupo x53 x10)))
      )
  and lookupoNotoOro y1 y2 y3 y4 =
    fresh (x42 x41 x43) (y1 === pair (y ()) y2 % x43 &&& notoOro y3 y4 y2 ||| (y1 === pair x41 x42 % x43 &&& lookupoNotoOro x43 y2 y3 y4))
  and notoOro y5 y6 y7 =
    y5 === !!true &&& (y6 === !!false) &&& (y7 === !!true) ||| (y5 === !!false &&& (y6 === !!true) &&& (y7 === !!false ||| (y7 === !!true)))
  and _lookupoNotoOro y8 y9 y10 y11 =
    fresh (x56 x55 x57) (y8 === pair (x ()) y9 % x57 &&& notoOro y9 y10 y11 ||| (y8 === pair x55 x56 % x57 &&& _lookupoNotoOro x57 y9 y10 y11))
  and lookupo y12 y13 = fresh (x69 x68 x70) (y12 === pair (y ()) y13 % x70 ||| (y12 === pair x68 x69 % x70 &&& lookupo x70 y13)) in
  loginto x0
