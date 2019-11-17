module LogicInt where

import Syntax
import Bool hiding (oro, ando, noto)
import List hiding (lit)

pair x y = C "pair" [x, y]

lookupo :: G a -> G a
lookupo =
  let subst = V "subst"
      var   = V "var"
      result = V "result"
  in
  Let (def "lookupo" ["subst", "var", "result"] $ (
    fresh ["key", "val", "tail"] $
    (subst === pair (V "key") (V "val") % V "tail" &&& (
      (var === V "key" &&& result === V "val")
      ||| call "lookupo" [V "tail", var, result])
    )
  ))

--
-- Test lookup
--

lookupoTest1 = lookupo $ fresh ["res"] $
  call "lookupo" [pair (C "x" []) trueo % pair (C "y" []) falso % nil, C "x" [], V "res"]

lookupoTest2 = lookupo $ fresh ["res"] $
  call "lookupo" [pair (C "x" []) trueo % pair (C "y" []) falso % nil, C "k" [], V "res"]

lookupoTest3 = lookupo $ fresh ["res", "st", "k"] $
  call "lookupo" [V "st", V "k", V "res"]

-----------------------------------------------------------

oro :: G a -> G a
oro =
  let result = V "result"
      a = V "a"
      b = V "b"
  in
  Let (def "oro" ["a", "b", "result"] $
    (a === trueo &&& result === trueo) |||
    (b === trueo &&& result === trueo) |||
    (result === falso)
  )

ando :: G a -> G a
ando =
  let result = V "result"
      a = V "a"
      b = V "b"
  in
  Let (def "ando" ["a", "b", "result"] $
    (a === trueo &&& b === trueo &&& result === trueo) |||
    (result === falso)
  )

noto :: G a -> G a
noto =
  let result = V "result"
      a = V "a"
      b = V "b"
  in
  Let (def "noto" ["a", "result"] $
    (a === trueo &&& result === falso) |||
    (result === trueo)
  )

{-
  Interpterer of logic formulas

  forumla :=
      lit Bool
    | var String
    | formula && formula
    | formula || formula
    | !formula
-}

lit b = C "lit" [b]
var x = C "var" [x]
neg x = C "neg" [x]
conj x y = C "conj" [x, y]
disj x y = C "disj" [x, y]

loginto :: G a -> G a
loginto =
  let subst = V "subst"
      formula = V "formula"
      result = V "result"
  in
  Let (def "loginto" ["subst", "formula", "result"] $
  fresh ["x", "l", "r", "rl", "rr"] (
      (formula === lit (result))
  ||| (formula === var (V "x") &&& call "lookupo" [subst, V "x", result])
  ||| (formula === neg (V "x")
       &&& call "loginto" [subst, V "x", V "rl"]
       &&& call "noto" [V "rl", result])
  ||| (formula === conj (V "l") (V "r")
       &&& call "loginto" [subst, V "l", V "rl"]
       &&& call "loginto" [subst, V "r", V "rr"]
       &&& call "ando" [V "rl", V "rr", result])
  ||| (formula === disj (V "l") (V "r")
       &&& call "loginto" [subst, V "l", V "rl"]
       &&& call "loginto" [subst, V "r", V "rr"]
       &&& call "oro" [V "rl", V "rr", result])
  )) . lookupo . noto . ando . oro

--
-- Test formulas
--
logintoTest1 = loginto $ fresh ["s", "r"] $ call "loginto" [V "s", lit trueo, V "r"]
logintoTest2 = loginto $ fresh ["s", "r"] $ call "loginto" [V "s", lit falso, V "r"]
logintoTest3 = loginto $ fresh ["s", "r"] $ call "loginto" [V "s", neg (lit falso), V "r"]
logintoTest4 = loginto $ fresh ["s", "r"] $ call "loginto" [V "s", conj (lit trueo) (lit falso), V "r"]
logintoTest5 = loginto $ fresh ["s", "r"] $ call "loginto" [V "s", disj (lit trueo) (lit falso), V "r"]
logintoTest6 = loginto $ fresh ["r", "x"] $ call "loginto" [(pair (C "x" []) trueo) % nil, var (C "x" []), V "rs"]
logintoTest7 = loginto $ fresh ["r", "x", "y"] $
  call "loginto" [(pair (C "y" []) trueo) % nil,
    conj (V "x") (neg (var $ C "y" [])),
    V "r"]

--
-- Log expressions
--

litX = lit (V "x")
litY = lit (V "y")

--
-- (x \/ y) /\ (\neg x \/ y)
--
logExpr1 = conj (disj litX litY) (disj (neg litX) litY)
logExpr2 = conj (conj (disj (conj litX (neg litY)) (conj (neg litX) litY)) litX) litY

--
-- Test queries
--
logintoQuery1 = loginto $ fresh ["s", "f", "r"] $ call "loginto" [V "s", V "f", V "r"]
logintoQuery2 = loginto $ fresh ["s", "f", "r", "x", "y"] $ call "loginto" [V "s", logExpr1, trueo]
logintoQuery3 = loginto $ fresh ["s", "f", "r", "x", "y"] $ call "loginto" [V "s", logExpr2, trueo]
