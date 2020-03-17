open GT
open OCanren
open Std
open Nat

let fstuDapp x0 x1 x2 x3 = let rec doubleAppendo y0 y1 y2 y3 = (fresh (x17 x18 x16 x6) ((((y0 === nil ()) &&& (appendo y1 y2 y3)) ||| ((y0 === (x6 % x16)) &&& (((x18 === (x6 % x17)) &&& (appendo x16 y1 x17)) &&& ((x18 === (x6 % x17)) &&& (appendo x18 y2 y3))))))) and appendo y4 y5 y6 = (fresh (x12 x11 x10) ((((y4 === nil ()) &&& (y6 === y5)) ||| (((y4 === (x10 % x11)) &&& (y6 === (x10 % x12))) &&& (appendo x11 y5 x12))))) in   (doubleAppendo x0 x1 x2 x3)
