module L = List

open OCanren
open OCanren.Nat


let rec add a b c =
   (a === zero &&& b === c)
   ||| (fresh (x y) (a === succ x &&& y === succ b &&& add x y c))

let _ = L.iter (fun r -> Printf.printf "%s\n" (show(Nat.logic) @@ c#reify  (Nat.reify))) 
       @@ RStream.take
       @@ run q (add zero zero q) (fun x -> x)
