open GT
open OCanren
open Std
open Nat

let sequMaxLen x0 x1 x2 = let rec maxLengtho y0 y1 y2 = (fresh (x17 x19 x18 x5) (((((y0 === nil ()) &&& (y2 === zero)) &&& (y1 === zero)) ||| (((y0 === (x5 % x18)) &&& (y2 === succ (x19))) &&& (((x17 === (x5 % x18)) &&& (maxo1 x17 y1)) &&& ((x17 === (x5 % x18)) &&& (lengtho x18 x19))))))) and maxo1 y3 y4 = (fresh (x37 x25 x24 x29) ((((y3 === nil ()) &&& (y4 === zero)) ||| (((y3 === (zero % x29)) &&& (maxo1 x29 y4)) ||| ((y3 === (x24 % x25)) &&& ((x24 === succ (x37)) &&& (_maxo1 x25 x37 y4))))))) and _maxo1 y5 y6 y7 = (fresh (x68 x67 x44 x53 x49 x41) ((((y5 === nil ()) &&& (y7 === succ (y6))) ||| (((y5 === (x41 % x49)) &&& ((_maxo1 x49 y6 y7) &&& ((x41 === zero) ||| ((x41 === succ (x53)) &&& (leo x53 y6))))) ||| ((y5 === (x44 % x67)) &&& ((x44 === succ (x68)) &&& ((_maxo1 x67 x68 y7) &&& (gto x68 y6)))))))) and leo y8 y9 = (fresh (x59 x58) (((y8 === zero) ||| (((y8 === succ (x58)) &&& (y9 === succ (x59))) &&& (leo x58 x59))))) and gto y10 y11 = (fresh (x73 x72 x71) ((((y10 === succ (x71)) &&& (y11 === zero)) ||| (((y10 === succ (x72)) &&& (y11 === succ (x73))) &&& (gto x72 x73))))) and lengtho y12 y13 = (fresh (x79 x78 x77) ((((y12 === nil ()) &&& (y13 === zero)) ||| (((y12 === (x77 % x78)) &&& (y13 === succ (x79))) &&& (lengtho x78 x79))))) in       (maxLengtho x0 x1 x2)
