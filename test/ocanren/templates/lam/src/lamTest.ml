module L = List

open GT
open OCanren
open Std
open Core

open TesterO

module GLam =
  struct
    module T =
      struct
        @type ('varname, 'self) t =
        | V of 'varname
        | App of 'self * 'self
        | Abs of 'varname * 'self
        with show, gmap

        let fmap f g x = gmap(t) f g x
      end

  include T
  include Fmap2(T)

  type rlam = (string, rlam) t
  type llam = (string logic, llam) t logic
  type flam = (rlam, llam) injected

  let v    s  = inj @@ distrib @@ V s
  let var  s  = inj @@ distrib @@ V s
  let app x y = inj @@ distrib @@ App (x,y)
  let abs x y = inj @@ distrib @@ Abs (x,y)
  let lam x y = inj @@ distrib @@ Abs (x,y)

  let rec show_rlam term = show(t) (show(string)) show_rlam term
  let rec show_llam term = show(logic) (show(t) (show(logic) @@ show string)show_llam) term
end

open GLam

let varX = !! "x"
let varY = !! "y"
let varF = !! "f"

let x = !! "x"

let rec glam_reifier : VarEnv.t -> GLam.flam -> GLam.llam = fun c x ->
  GLam.reify OCanren.reify glam_reifier c x

let rec substo l x a l' =
  conde [
    fresh (y) (l === v y) (y === x) (l' === a);
    fresh (m n m' n')
      (l  === app m n)
      (l' === app m' n')
      (substo m x a m')
      (substo n x a n');
    fresh (v b)
      (l === abs v b)
      (conde [
         (x  === v) &&& (l' === l);
         fresh (b') (l' === abs v b') (substo b x a b')
       ])
  ]

let rec evalo m n =
  conde [
    fresh (x)
      (m === v x)
      (n === m);
    fresh (x l)
      (m === abs x l)
      (n === m);
    fresh (f a f' a')
      (m === app f a)
      (evalo f f')
      (evalo a a')
      (conde [
         fresh (x l l')
           (f' === abs x l)
           (substo l x a' l')
           (evalo l' n);
         fresh (p q) (f' === app p q) (n === app f' a');
         fresh (x) (f' === v x) (n === app f' a')
       ])
  ]

let lamS x0 =
  let rec slamo y0 = fresh (x41 x26) (y0 === abs varY (var varY) ||| (slamoSubsto x26 y0 ||| slamoSlamoSlamo x26 x41 y0))
  and slamoSubsto y1 y2 = y1 === var varX &&& (y2 === abs varY (var varY))
  and slamoSlamoSlamo y3 y4 y5 =
    fresh (x93 x78)
      ( y3 === var varX
      &&& (y4 === abs varX x78)
      &&& slamoSubsto x78 y5
      ||| (y3 === var varX &&& (y4 === abs varX x78) &&& slamoSlamoSlamo x78 x93 y5) )
  in
  slamo x0

let lamS2 x0 =
  let rec slamo y0 =
    fresh (x9 x109 x100 x8 x7 x6 x5 x3)
      ( y0 === lam x x3 &&& _slamo x3
      ||| ( y0 === app x5 x6
          &&& (x5 === lam x7 x8)
          &&& ( x8 === var x7
              &&& (x6 === lam x (var x))
              ||| (x8 === lam x7 (var x) &&& (x7 === x) ||| (x8 === lam x x100 &&& substo x100 x7 x6)) )
          ||| (y0 === app x5 x6 &&& (x109 === app x9 x6 &&& slamo x109 &&& __slamo x5 x9)) ) )
  and _slamo y1 =
    fresh (x20 x36 x19 x18 x17 x16)
      ( y1 === var x
      ||| ( y1 === app x16 x17
          &&& (x16 === lam x18 x19)
          &&& substo x19 x18 x17
          ||| (y1 === app x16 x17 &&& (x36 === app x20 x17 &&& _slamo x36 &&& __slamo x16 x20)) ) )
  and substo y2 y3 y4 = y2 === var y3 &&& (y4 === var x)
  and __slamo y5 y6 =
    fresh (x48 x47 x46 x45 x44 x43 x42 x41 x40)
      ( y5 === var x40 &&& (y6 === y5)
      ||| ( y5 === lam x41 x42
          &&& (y6 === lam x41 x43)
          &&& __slamo x42 x43
          ||| ( y5 === app x44 x45
              &&& (x44 === lam x46 x47)
              &&& _substo x47 x46 x45 y6
              ||| (y5 === app x44 x45 &&& slamoSlamo x44 x48 x45 y6) ) ) )
  and _substo y7 y8 y9 y10 =
    fresh (x62 x60 x61 x58 x59 x57 x56)
      ( y7 === var y8 &&& (y10 === y9)
      ||| ( y7 === app x56 x57
          &&& (y10 === app x59 x58)
          &&& (_substo x56 y8 y9 x59 &&& _substo x57 y8 y9 x58)
          ||| ( y7 === lam y8 x61 &&& (y10 === y7)
              ||| (y7 === lam x60 x61 &&& (y10 === lam x60 x62) &&& _substo x61 y8 y9 x62) ) ) )
  and slamoSlamo y11 y12 y13 y14 =
    fresh (x87 x86 x85)
      (y12 === lam x85 x86 &&& _substo x86 x85 y13 y14 ||| slamoSlamo y12 x87 y13 y14 &&& __slamo y11 y12)
  in
  slamo x0

let runL n = runR glam_reifier show_rlam show_llam n

let _ =
(*  run_exn show_rlam 1 q qh (REPR (fun q -> evalo (abs varX (v varX)) q)); *)
  runL 4 q qh (REPR (fun q -> lamS2 q));
  ()


(*
let _ =
  run_exn show_rlam 1    q   qh (REPR (fun q   -> substo (v varX) varX (v varY) q                       ));
  run_exn show_rlam 1    q   qh (REPR (fun q   -> evalo (abs varX (v varX)) q                           ));
  run_exn show_rlam 2    q   qh (REPR (fun q   -> evalo (abs varX (v varX)) q                           ));
  run_exn show_rlam 1    q   qh (REPR (fun q   -> evalo (app (abs varX (v varX)) (v varY))        q     ));
  run_exn show_rlam 1    q   qh (REPR (fun q   -> evalo (app (abs varX (v varX))        q) (v varY)     ));
  run_exn show_rlam 1    q   qh (REPR (fun q   -> evalo (app (abs varX        q) (v varY)) (v varY)     ));
  run_exn show_rlam 1    q   qh (REPR (fun q   -> evalo (app            (v varX) (v varX)) q            ));
  run_exn show_rlam 1    q   qh (REPR (fun q   -> evalo (v varX)    q                                   ));
  ()
*)
(*

let _withFree =
  runL 1     q   qh (REPR (fun q     -> evalo (app q (v varX)) (v varX)             ));
  runL 1    qr  qrh (REPR (fun q r   -> evalo (app r q)        (v varX)             ))
*)
  (*runL 2    qrs qrsh (REPR (fun q r s -> a_la_quine q r s                            ))*)
