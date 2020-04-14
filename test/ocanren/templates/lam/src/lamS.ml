open GT
open OCanren
open Std
open Nat

let lamS x0 =
  let rec slamo y0 =
    fresh (x9 x109 x100 x8 x7 x6 x5 x3)
      ( y0 === lam x x3 &&& _slamo x3
      ||| ( y0 === app x5 x6
          &&& (x5 === lam x7 x8)
          &&& ( x8 === var x7
              &&& (x6 === lam x (var x))
              ||| (x8 === lam x7 (var x) &&& (x7 === x) ||| (x8 === lam x x100 &&& substo x100 x7 x6)) )
          ||| (y0 === app x5 x6 &&& (x109 === app x9 x6 &&& slamo x109 &&& __slamo x5 x9)) ) )
  and _slamo y1 =
    fresh (x20 x36 x19 x18 x17 x16)
      ( y1 === var x
      ||| ( y1 === app x16 x17
          &&& (x16 === lam x18 x19)
          &&& substo x19 x18 x17
          ||| (y1 === app x16 x17 &&& (x36 === app x20 x17 &&& _slamo x36 &&& __slamo x16 x20)) ) )
  and substo y2 y3 y4 = y2 === var y3 &&& (y4 === var x)
  and __slamo y5 y6 =
    fresh (x48 x47 x46 x45 x44 x43 x42 x41 x40)
      ( y5 === var x40 &&& (y6 === y5)
      ||| ( y5 === lam x41 x42
          &&& (y6 === lam x41 x43)
          &&& __slamo x42 x43
          ||| ( y5 === app x44 x45
              &&& (x44 === lam x46 x47)
              &&& _substo x47 x46 x45 y6
              ||| (y5 === app x44 x45 &&& slamoSlamo x44 x48 x45 y6) ) ) )
  and _substo y7 y8 y9 y10 =
    fresh (x62 x60 x61 x58 x59 x57 x56)
      ( y7 === var y8 &&& (y10 === y9)
      ||| ( y7 === app x56 x57
          &&& (y10 === app x59 x58)
          &&& (_substo x56 y8 y9 x59 &&& _substo x57 y8 y9 x58)
          ||| ( y7 === lam y8 x61 &&& (y10 === y7)
              ||| (y7 === lam x60 x61 &&& (y10 === lam x60 x62) &&& _substo x61 y8 y9 x62) ) ) )
  and slamoSlamo y11 y12 y13 y14 =
    fresh (x87 x86 x85)
      (y12 === lam x85 x86 &&& _substo x86 x85 y13 y14 ||| slamoSlamo y12 x87 y13 y14 &&& __slamo y11 y12)
  in
  slamo x0
