open GT
open OCanren
open Std
open Core
open Nat

@type ('a, 'b) uterm =
  | Var  of 'a
  | Constr of 'a * 'b
  with show, gmap

@type f = (Nat.logic, f) uterm logic' with show, gmap
@type answer = f list with show, gmap

module F = Fmap2 (struct type ('a, 'b) t = ('a, 'b) uterm let fmap f g x = gmap(uterm) f g x end)

let rec reify_f f = F.reify reify_f reify f

let constr x y = Logic.inj @@ F.distrib (Constr (x, y))
let var_ x  = Logic.inj @@ F.distrib (Var x)
