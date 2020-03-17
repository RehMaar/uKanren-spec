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

  let v   s   = inj @@ distrib @@ V s
  let app x y = inj @@ distrib @@ App (x,y)
  let abs x y = inj @@ distrib @@ Abs (x,y)

  let rec show_rlam term = show(t) (show(string)) show_rlam term
  let rec show_llam term = show(logic) (show(t) (show(logic) @@ show string)show_llam) term
end

open GLam

let varX = !! "x"
let varY = !! "y"
let varF = !! "f"

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

let _ =
  run_exn show_rlam 1 q qh (REPR (fun q -> evalo (abs varX (v varX)) q));
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
let runL n = runR glam_reifier show_rlam show_llam n

let _withFree =
  runL 1     q   qh (REPR (fun q     -> evalo (app q (v varX)) (v varX)             ));
  runL 1    qr  qrh (REPR (fun q r   -> evalo (app r q)        (v varX)             ))
*)
  (*runL 2    qrs qrsh (REPR (fun q r s -> a_la_quine q r s                            ))*)
