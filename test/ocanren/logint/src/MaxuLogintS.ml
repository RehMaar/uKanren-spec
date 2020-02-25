open GT
open OCanren
open Std
open Nat

open LogicExpr

let maxuLogintS x0 =
  let rec loginto y0 =
    fresh
      (x94 x93 x85 x84 x86 x75 x74 x60 x59 x61 x50 x49 x35 x34 x16 x36)
      ( y0
      === pair (y ()) !!true % x36
      &&& lookupoNoto x36 x16
      ||| (y0 === pair x34 x35 % x49 &&& (x50 === pair x34 x35 % x49 &&& lookupo x49 &&& (x50 === pair x34 x35 % x49 &&& lookupoNoto x50 x16)))
      ||| ( y0
          === pair (y ()) !!false % x61
          &&& _lookupoNoto x61 x16
          ||| (y0 === pair x59 x60 % x74 &&& (x75 === pair x59 x60 % x74 &&& _lookupo x74 &&& (x75 === pair x59 x60 % x74 &&& _lookupoNoto x75 x16)))
          ||| ( y0
              === pair (y ()) !!true % x86
              &&& _lookupoNoto x86 x16
              ||| (y0 === pair x84 x85 % x93 &&& (x94 === pair x84 x85 % x93 &&& lookupo x93 &&& (x94 === pair x84 x85 % x93 &&& _lookupoNoto x94 x16))) ) ) )
  and lookupoNoto y1 y2 = fresh (x43 x42 x44) (y1 === pair (x ()) y2 % x44 &&& (y2 === !!true) ||| (y1 === pair x42 x43 % x44 &&& lookupoNoto x44 y2))
  and lookupo y3 = fresh (x53 x52 x54) (y3 === pair (y ()) !!true % x54 ||| (y3 === pair x52 x53 % x54 &&& lookupo x54))
  and _lookupoNoto y4 y5 = fresh (x68 x67 x69) (y4 === pair (x ()) y5 % x69 &&& (y5 === !!false) ||| (y4 === pair x67 x68 % x69 &&& _lookupoNoto x69 y5))
  and _lookupo y6 = fresh (x78 x77 x79) (y6 === pair (y ()) !!false % x79 ||| (y6 === pair x77 x78 % x79 &&& _lookupo x79)) in
  loginto x0
