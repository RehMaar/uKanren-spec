open OCanren
open GT
open Std
open Nat
open UnifyTerm

let minuUnify x0 x1 x2 = let rec check_uni y0 y1 y2 = (fresh (x140 x138 x139 x126 x127 x123 x122 x120 x121 x82 x108 x109 x102 x93 x83 x77 x78 x21 x20 x73 x72 x17 x16 x15 x62 x63 x12 x11 x10 x31 x44 x29 x43 x7 x6 x5 x4) (((((y1 === (constr x4 x5)) &&& (y2 === (constr x6 x7))) &&& ((((x5 === nil ()) &&& (x7 === nil ())) &&& (eq_nat x4 x6)) ||| (((x5 === (x43 % x29)) &&& (x7 === (x44 % x31))) &&& ((check_uni y0 x43 x44) &&& ((forall2 y0 x29 x31) &&& (eq_nat x4 x6)))))) ||| ((((y1 === (var_ x10)) &&& (y2 === (constr x11 x12))) &&& (((x63 === (constr x11 x12)) &&& (check_uni y0 x62 x63)) &&& (get_term x10 y0 x62))) ||| ((((y1 === (constr x15 x16)) &&& (y2 === (var_ x17))) &&& (((x72 === (constr x15 x16)) &&& (check_uni y0 x72 x73)) &&& (get_term x17 y0 x73))) ||| ((((y1 === (var_ x20)) &&& (y2 === (var_ x21))) &&& (((x78 === (var_ x21)) &&& (check_uni y0 x77 x78)) &&& (get_term x20 y0 x77))) ||| (((y1 === (var_ x20)) &&& (y2 === (var_ x21))) &&& (((y0 === nil ()) &&& (eq_nat x20 x21)) ||| ((((y0 === (none () % x83)) &&& (x20 === zero)) &&& ((x21 === zero) ||| ((x21 === succ (x93)) &&& (((x83 === (x102 % x109)) &&& (x93 === succ (x108))) &&& (_get_term x108 x109))))) ||| (((y0 === (x82 % x121)) &&& (x20 === succ (x120))) &&& ((((x122 === (x82 % x121)) &&& (x123 === succ (x120))) &&& (_get_term x120 x121)) &&& (((x122 === (x82 % x121)) &&& (x123 === succ (x120))) &&& (((x122 === nil ()) &&& (eq_nat x123 x21)) ||| ((((x122 === (none () % x127)) &&& (x21 === zero)) &&& (x123 === zero)) ||| (((x122 === (x126 % x139)) &&& (x21 === succ (x138))) &&& (((x140 === succ (x138)) &&& (_get_term x138 x139)) &&& ((x140 === succ (x138)) &&& (eq_nat x123 x140)))))))))))))))))) and eq_nat y3 y4 = (fresh (x39 x38) ((((y3 === zero) &&& (y4 === zero)) ||| (((y3 === succ (x38)) &&& (y4 === succ (x39))) &&& (eq_nat x38 x39))))) and forall2 y5 y6 y7 = (fresh (x51 x57 x49 x56) ((((y6 === nil ()) &&& (y7 === nil ())) ||| (((y6 === (x56 % x49)) &&& (y7 === (x57 % x51))) &&& ((check_uni y5 x56 x57) &&& (forall2 y5 x49 x51)))))) and get_term y8 y9 y10 = (fresh (x68 x67 x66) (((((y9 === (x66 % x67)) &&& (y8 === zero)) &&& (x66 === (some y10))) ||| (((y9 === (x66 % x67)) &&& (y8 === succ (x68))) &&& (get_term x68 x67 y10))))) and _get_term y11 y12 = (fresh (x114 x112 x113) (((y12 === nil ()) ||| (((y12 === (none () % x113)) &&& (y11 === zero)) ||| (((y12 === (x112 % x113)) &&& (y11 === succ (x114))) &&& (_get_term x114 x113)))))) in      (check_uni x0 x1 x2)
