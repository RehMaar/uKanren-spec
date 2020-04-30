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

let quine x0 = let rec slamo y0 = (fresh (x3 x2 x94 x93 x46 x9 x45 x18 x17 x8 x7 x6 x5 x1) (((y0 === (var x1)) ||| ((((y0 === (app x5 x6)) &&& (x5 === (lam x7 x8))) &&& ((x8 === (app x17 x18)) &&& (((x17 === (var x7)) &&& (x6 === (lam x7 ((app x17 x18))))) &&& (x18 === (var x7))))) ||| (((y0 === (app x5 x6)) &&& ((((x45 === (app x9 x6)) &&& (x46 === (app x5 x6))) &&& (_slamo x45 x46)) &&& (((x93 === (app x9 x6)) &&& (x94 === (app x5 x6))) &&& (_slamo x93 x94)))) ||| ((y0 === (lam x2 x3)) &&& (slamo x3))))))) and _slamo y1 y2 = (fresh (x88 x56 x83 x55 x54 x53 x52 x51 x50 x49 x48) ((((y1 === (var x48)) &&& (y2 === y1)) ||| ((((y1 === (lam x49 x50)) &&& (y2 === (lam x49 x51))) &&& (_slamo x50 x51)) ||| ((((y1 === (app x52 x53)) &&& (x52 === (lam x54 x55))) &&& (substo x55 x54 x53 y2)) ||| ((y1 === (app x52 x53)) &&& (((x83 === (app x56 x53)) &&& (_slamo x83 y2)) &&& ((x88 === (app x56 x53)) &&& (_slamo x88 y2))))))))) and substo y3 y4 y5 y6 = (fresh (x70 x68 x69 x66 x67 x65 x64) ((((y3 === (var y4)) &&& (y6 === y5)) ||| ((((y3 === (app x64 x65)) &&& (y6 === (app x67 x66))) &&& ((substo x64 y4 y5 x67) &&& (substo x65 y4 y5 x66))) ||| (((y3 === (lam y4 x69)) &&& (y6 === y3)) ||| (((y3 === (lam x68 x69)) &&& (y6 === (lam x68 x70))) &&& (((y4 =/= x68) &&& (y4 =/= x68)) &&& (substo x69 y4 y5 x70)))))))) in    (slamo x0)

let runL n = runR glam_reifier show_rlam show_llam n

let _ =
(*  run_exn show_rlam 1 q qh (REPR (fun q -> evalo (abs varX (v varX)) q)); *)
  runL 4 q qh (REPR (fun q -> evalo q q));
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
