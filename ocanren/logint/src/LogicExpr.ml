open GT
open OCanren
open Std

@type ('a, 'l) expr = 
    Lit of 'a
  | Var of 'a
  | Conj of 'l * 'l
  | Disj of 'l * 'l
  | Not  of 'l
  with show, gmap, eq, compare, foldl, foldr

@type 'a logic'     = 'a logic              with show, gmap, eq, compare, foldl, foldr
@type ('a, 'l) t    = ('a, 'l) expr         with show, gmap, eq, compare, foldl, foldr

let logic' = logic
           
module X =
  struct
    @type ('a,'b) t = ('a, 'b) expr with show, gmap, eq, compare, foldl, foldr
    let fmap f g x = GT.gmap expr f g x
  end

module F = Fmap2 (X)

let f a = Logic.inj @@ F.distrib a

let lit a    = f (Lit a)
let var a    = f (Var a)
let neg a    = f (Not a)
let conj a b = f (Conj (a, b))
let disj a b = f (Disj (a, b))
