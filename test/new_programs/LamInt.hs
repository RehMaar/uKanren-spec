module LamInt where

import Syntax
import Bool
import List

pair x y = C "pair" [x, y]

lookupo :: G a -> G a
lookupo =
  let subst = V "subst"
      var   = V "var"
      result = V "result"
  in
  Let (def "lookupo" ["subst", "var", "result"] (
    fresh ["key", "val", "tail"]
    (subst === pair (V "key") (V "val") % V "tail" &&& (
      (var === V "key" &&& result === V "val")
      ||| (
       -- NOTE: diseq
       var =/= V "key" &&&
       call "lookupo" [V "tail", var, result]))
    )
  ))


app lf rg = C "app" [lf, rg]
lam hd bd = C "lam" [hd, bd]
var x     = C "var" [x]


{-
Simple lambda calculus interpreter.

NOTE: Please, do not use clashed variables!
-}

substo :: G a -> G a
substo = Let (def "substo" ["expr", "val", "term", "result"] $
    fresh ["y"] (
       (expr === var (V "y")) &&& (V "y" === val) &&& (result === term))
    |||
    fresh ["le", "re", "rt", "lt"] (
      expr   === app (V "le") (V "re") &&&
      result === app (V "lt") (V "rt") &&&
      call "substo" [V "le", val, term, V "lt"] &&&
      call "substo" [V "re", val, term, V "rt"])
    |||
    fresh ["hd", "bd"] (
      expr === lam (V "hd") (V "bd") &&&
      (((val === V "hd") &&& (expr === result)) |||
       fresh ["bd'"]
        (
         -- NOTE: diseq
         val =/= V "hd" &&&
         result === lam (V "hd") (V "bd'") &&&
         call "substo" [V "bd", val, term, V "bd'"]
      )))
  )
  where
    (expr, val, term, result) = (V "expr", V "val", V "term", V "result")

slamo :: G a -> G a
slamo =
  Let (def "slamo" ["expr", "result"] $
    -- expr is var
    fresh ["v"]
      (expr === var (V "v") &&& expr === result)
    -- expr is abstraction
    |||
    fresh ["hd", "body", "reduced"]
      (expr === lam (V "hd") (V "body") &&&
       call "slamo" [V "body", V "reduced"] &&&
       result === lam (V "hd") (V "reduced")
      )
    -- expr is application
    |||
    fresh ["fun", "arg", "hd", "body", "rfun", "app"]
      (expr === app (V "fun") (V "arg") &&&
        (
          -- If fun is lambda head body then body[hd -> arg]
          ((V "fun" === lam (V "hd") (V "body")) &&&
            call "substo" [V "body", V "hd", V "arg", result]) |||
          -- If fun isn't an abstraction then reduce it!
          -- NOTE: diseq
          ((V "fun" === lam (V "hd") (V "body")) &&&
           call "slamo" [V "fun", V "rfun"] &&&
           V "app" === app (V "rfun") (V "arg") &&&
           call "slamo" [V "app", result])
        )
      )
  ) . substo
  where
    expr = V "expr"
    result = V "result"

slamoEnv ="open GT\nopen OCanren\nopen Std\nopen Nat\nopen GLam"

{-
var x -> var x

lam x body -> lam x (step body)

app (lam x b) r -> b[x -> r]

app l r -> app l (step r)

-}
{-slamoStep :: G a -> G a
slamoStep =
  Let (def "slamoStep" ["expr", "result"] $
	  fresh ["v"]
	   (expr === var (V "v") &&& expr === result)
	  |||
    fresh ["hd", "body", "reduced"]
      (expr === lam (V "hd") (V "body") &&&
       call "slamoStep" [V "body", V "reduced"] &&&
       result === lam (V "hd") (V "reduced")
      )
    |||
    fresh ["fun", "arg", "hd", "body", "rfun", "app"]
      (expr === app (V "fun") (V "arg") &&&
        (
          -- If fun is lambda head body then body[hd -> arg]
          ((V "fun" === lam (V "hd") (V "body")) &&&
            call "substo" [V "body", V "hd", V "arg", result]) |||
          -- If fun isn't an abstraction then reduce it!
          (call "slamo" [V "fun", V "rfun"] &&&
           V "app" === app (V "rfun") (V "arg") &&&
           call "slamo" [V "app", result])
        )
      )
  ) . Let (def "slamoStep'" ["expr", "result"] $

  )-}

--------------------------------------------------------------

val x = C x []

lamId = lam (val "x") (var (val "x"))
lamIdY = lam (val "y") (var (val "y"))

slamoQuery1 = slamo $ fresh ["r"] $ call "slamo" [lamId,V "r"]
slamoQuery2 = slamo $ fresh ["r"] $ call "slamo" [app lamId lamIdY, V "r"]
slamoQueryB = slamo $ fresh ["r"] $ call "slamo" [V "r",lamId]
slamoQueryId = slamo $ fresh ["p1", "p2"] $ call "slamo" [V "p1", V "p2"]
slamoQueryQuine = slamo $ fresh ["p1"] $ call "slamo" [V "p1", V "p1"]

substoQuery1 = substo $ fresh ["a", "b", "c", "d"] $ call "substo" [V "a", V "b", V "c", V "d"]

-- Запрос: генерировать редуцируемые за два шага термы определённого типа
--
