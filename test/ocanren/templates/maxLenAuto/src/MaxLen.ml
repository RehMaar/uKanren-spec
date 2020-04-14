open GT
open OCanren
open Std
open Nat

let maxLen x0 x1 x2 =
  let rec maxLengtho y0 y1 y2 = maxo y0 y1 &&& lengtho y0 y2
  and maxo y3 y4 = maxo1 y3 zero y4
  and maxo1 y5 y6 y7 =
    y5 === nil () &&& (y7 === y6)
    ||| (fresh (z t h) (y5 === h % t &&& (leo h y6 !!true &&& maxo1 t y6 y7)) ||| fresh (z t h) (y5 === h % t &&& (gto h y6 !!true &&& maxo1 t h y7)))
  and leo y8 y9 y10 =
    y8 === zero &&& (y10 === !!true)
    ||| (fresh (zz) (y8 === succ zz &&& (y9 === zero &&& (y10 === !!false))) ||| fresh (y' x') (y8 === succ x' &&& (y9 === succ y' &&& leo x' y' y10)))
  and gto y11 y12 y13 =
    fresh (zz) (y11 === succ zz &&& (y12 === zero &&& (y13 === !!true)))
    ||| (y11 === zero &&& (y13 === !!false) ||| fresh (y' x') (y11 === succ x' &&& (y12 === succ y' &&& gto x' y' y13)))
  and lengtho y14 y15 = y14 === nil () &&& (y15 === zero) ||| fresh (z t h) (y14 === h % t &&& (y15 === succ z &&& lengtho t z)) in
  maxLengtho x0 x1 x2
