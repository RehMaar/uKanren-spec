open GT
open OCanren
open Std
open Nat

let nrcuIsPath x0 x1 = let rec isPath y0 y1 = (fresh (x11 x5 x4 x3 x2) (((y0 === nil ()) ||| ((y0 === (x2 % nil ())) ||| ((y0 === (x3 % (x4 % x5))) &&& (((x11 === (x4 % x5)) &&& (isPath x11 y1)) &&& (elem x3 x4 y1))))))) and elem y2 y3 y4 = (fresh (x49 x47 x46 x22 x21 x15 x14) ((((y4 === (x14 % x15)) &&& ((x14 === (pair x21 x22)) &&& (eqNatEqNat y2 x21 y3 x22))) ||| ((y4 === (x14 % x15)) &&& ((elem y2 y3 x15) &&& (((x14 === (pair x46 x47)) &&& (_eqNatEqNat y2 x46 y3 x47 x49)) ||| ((x14 === (pair x46 x47)) &&& ((eqNat y2 x46) &&& (__eqNat y3 x47))))))))) and eqNatEqNat y5 y6 y7 y8 = (fresh (x30 x29) (((((y5 === zero) &&& (y6 === zero)) &&& (eqNat y7 y8)) ||| (((y5 === succ (x29)) &&& (y6 === succ (x30))) &&& (eqNatEqNat x29 x30 y7 y8))))) and eqNat y9 y10 = (fresh (x36 x35) ((((y9 === zero) &&& (y10 === zero)) ||| (((y9 === succ (x35)) &&& (y10 === succ (x36))) &&& (eqNat x35 x36))))) and _eqNatEqNat y11 y12 y13 y14 y15 = (fresh (x55 x54 x53 x52) (((((y11 === succ (x52)) &&& (y12 === zero)) &&& (_eqNat y13 y14 y15)) ||| ((((y11 === zero) &&& (y12 === succ (x53))) &&& (_eqNat y13 y14 y15)) ||| (((y11 === succ (x54)) &&& (y12 === succ (x55))) &&& (_eqNatEqNat x54 x55 y13 y14 y15)))))) and _eqNat y16 y17 y18 = (fresh (x61 x60 x59 x58) (((((y16 === zero) &&& (y17 === zero)) &&& (y18 === !!true)) ||| ((((y16 === succ (x58)) &&& (y17 === zero)) &&& (y18 === !!false)) ||| ((((y16 === zero) &&& (y17 === succ (x59))) &&& (y18 === !!false)) ||| (((y16 === succ (x60)) &&& (y17 === succ (x61))) &&& (_eqNat x60 x61 y18))))))) and __eqNat y19 y20 = (fresh (x75 x74 x73 x72) ((((y19 === succ (x72)) &&& (y20 === zero)) ||| (((y19 === zero) &&& (y20 === succ (x73))) ||| (((y19 === succ (x74)) &&& (y20 === succ (x75))) &&& (__eqNat x74 x75)))))) in        (isPath x0 x1)
