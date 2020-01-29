open GT
open OCanren
open Std
open Core

@type ('a, 'b) fa =
  | Conj of 'a * 'a
  | Disj of 'a * 'a
  | Neg  of 'a
  | Var  of 'b 
  | LTrue 
  | LFalse 
  with show, gmap

@type name   = X | Y | Z with show, gmap
@type f      = (f, name logic) fa logic with show, gmap
@type answer = ocanren ((name * bool) list) with show

module F = Fmap2 (struct type ('a, 'b) t = ('a, 'b) fa let fmap f g x = gmap(fa) f g x end)
            
let conj   x y = inj @@ F.distrib (Conj (x, y))
let disj   x y = inj @@ F.distrib (Disj (x, y))
let var    x   = inj @@ F.distrib (Var x)
let neg    x   = inj @@ F.distrib (Neg x)
let ltrue  ()  = inj @@ F.distrib LTrue 
let lfalse ()  = inj @@ F.distrib LFalse

let x () = !! X
let y () = !! Y
let z () = !! Z
