open GT
open OCanren
open Std
open Nat

let fuluDapp x0 x1 x2 x3 = let rec doubleAppendo y0 y1 y2 y3 = (fresh (x4) ((appendoAppendo y0 y1 x4 y2 y3))) and appendoAppendo y4 y5 y6 y7 y8 = (fresh (x8 x7 x6 x11 x10 x9) ((((((y4 === nil ()) &&& (y6 === y5)) &&& (y5 === nil ())) &&& (y8 === y7)) ||| ((((((y4 === nil ()) &&& (y6 === y5)) &&& (y5 === (x9 % x10))) &&& (y8 === (x9 % x11))) &&& (appendo x10 y7 x11)) ||| ((((y4 === (x6 % x7)) &&& (y6 === (x6 % x8))) &&& (y8 === (x6 % x11))) &&& (appendoAppendo x7 y5 x8 y7 x11)))))) and appendo y9 y10 y11 = (fresh (x16 x15 x14) ((((y9 === nil ()) &&& (y11 === y10)) ||| (((y9 === (x14 % x15)) &&& (y11 === (x14 % x16))) &&& (appendo x15 y10 x16))))) in    (doubleAppendo x0 x1 x2 x3)
