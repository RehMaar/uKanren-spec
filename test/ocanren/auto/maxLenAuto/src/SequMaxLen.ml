open GT
open OCanren
open Std
open Nat

let sequMaxLen x0 x1 x2 = let rec maxLengtho y0 y1 y2 = (fresh (x17 x19 x18 x5) (((((y0 === nil ()) &&& (y2 === zero)) &&& (y1 === zero)) ||| (((y0 === (x5 % x18)) &&& (y2 === succ (x19))) &&& (((x17 === (x5 % x18)) &&& (maxo1 x17 y1)) &&& ((x17 === (x5 % x18)) &&& (lengtho x18 x19))))))) and maxo1 y3 y4 = (fresh (x36 x25 x24 x22) ((((y3 === nil ()) &&& (y4 === zero)) ||| (((y3 === (zero % x22)) &&& (maxo1 x22 y4)) ||| ((y3 === (x24 % x25)) &&& ((x24 === succ (x36)) &&& (_maxo1 x25 x36 y4))))))) and _maxo1 y5 y6 y7 = (fresh (x62 x44 x43 x51 x41 x40) ((((y5 === nil ()) &&& (y7 === succ (y6))) ||| (((y5 === (x40 % x41)) &&& ((_maxo1 x41 y6 y7) &&& ((x40 === zero) ||| ((x40 === succ (x51)) &&& (leo x51 y6))))) ||| ((y5 === (x43 % x44)) &&& ((x43 === succ (x62)) &&& ((_maxo1 x44 x62 y7) &&& (gto x62 y6)))))))) and leo y8 y9 = (fresh (x57 x56) (((y8 === zero) ||| (((y8 === succ (x56)) &&& (y9 === succ (x57))) &&& (leo x56 x57))))) and gto y10 y11 = (fresh (x69 x68 x67) ((((y10 === succ (x67)) &&& (y11 === zero)) ||| (((y10 === succ (x68)) &&& (y11 === succ (x69))) &&& (gto x68 x69))))) and lengtho y12 y13 = (fresh (x75 x74 x73) ((((y12 === nil ()) &&& (y13 === zero)) ||| (((y12 === (x73 % x74)) &&& (y13 === succ (x75))) &&& (lengtho x74 x75))))) in       (maxLengtho x0 x1 x2)
