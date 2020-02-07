open GT
open OCanren
open Std
open Core

@type ('a, 'b) expr =
  | Conj of 'a * 'a
  | Disj of 'a * 'a
  | Neg  of 'a
  | Var  of 'b 
  | LTrue 
  | LFalse 
  with show, gmap

@type name   = X | Y | Z with show, gmap
@type f      = (f, name logic) expr logic with show, gmap
@type answer = ocanren ((name * bool) list) with show

module F = Fmap2 (struct type ('a, 'b) t = ('a, 'b) expr let fmap f g x = gmap(expr) f g x end)
            

let toL x = inj @@ F.distrib x

let conj   x y = inj @@ F.distrib (Conj (x, y))
let disj   x y = inj @@ F.distrib (Disj (x, y))
let var    x   = inj @@ F.distrib (Var x)
let neg    x   = inj @@ F.distrib (Neg x)
let ltrue  ()  = inj @@ F.distrib LTrue 
let lfalse ()  = inj @@ F.distrib LFalse

let x () = !! X
let y () = !! Y
let z () = !! Z
