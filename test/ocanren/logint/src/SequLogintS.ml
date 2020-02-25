open GT
open OCanren
open Std
open Nat

open LogicExpr

let sequLogintS x0 =
  let rec loginto y0 =
    fresh
      (x121 x122 x113 x112 x114 x88 x89 x75 x74 x76 x49 x50 x36 x35 x37)
      ( y0
      === pair (y ()) !!true % x37
      &&& lookupo x37
      ||| (y0 === pair x35 x36 % x50 &&& (x49 === pair x35 x36 % x50 &&& lookupo x49 &&& (x49 === pair x35 x36 % x50 &&& _lookupo x50)))
      ||| ( y0
          === pair (y ()) !!false % x76
          &&& __lookupo x76
          ||| (y0 === pair x74 x75 % x89 &&& (x88 === pair x74 x75 % x89 &&& __lookupo x88 &&& (x88 === pair x74 x75 % x89 &&& ___lookupo x89)))
          ||| ( y0
              === pair (y ()) !!true % x114
              &&& __lookupo x114
              ||| (y0 === pair x112 x113 % x122 &&& (x121 === pair x112 x113 % x122 &&& __lookupo x121 &&& (x121 === pair x112 x113 % x122 &&& _lookupo x122)))
              ) ) )
  and lookupo y1 = fresh (x44 x43 x45) (y1 === pair (x ()) !!true % x45 ||| (y1 === pair x43 x44 % x45 &&& lookupo x45))
  and _lookupo y2 = fresh (x54 x53 x55) (y2 === pair (y ()) !!true % x55 ||| (y2 === pair x53 x54 % x55 &&& _lookupo x55))
  and __lookupo y3 = fresh (x83 x82 x84) (y3 === pair (x ()) !!false % x84 ||| (y3 === pair x82 x83 % x84 &&& __lookupo x84))
  and ___lookupo y4 = fresh (x93 x92 x94) (y4 === pair (y ()) !!false % x94 ||| (y4 === pair x92 x93 % x94 &&& ___lookupo x94)) in
  loginto x0
