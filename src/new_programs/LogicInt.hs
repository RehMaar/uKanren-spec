module LogicInt where

import Syntax
import Bool hiding (oro, ando, noto)
import List hiding (lit)

pair x y = C "pair" [x, y]

{-
lookupo([(K, V) | T], K, V).
lookupo([H | T], K, R) :- lookupo(T, K, R).
-}
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

lookupoTest4 = lookupo $ fresh ["res", "tail"] $
  call "lookupo" [pair (C "x" []) trueo % (V "tail"), C "x" [], V "res"]

-------------------------------------------------------------

true = C "ltrue" []
false = C "lfalse" []
var x = C "var" [x]
neg x = C "neg" [x]
conj x y = C "conj" [x, y]
disj x y = C "disj" [x, y]


{-
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
    -- TODO: possible problems
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
-}

oro :: G a -> G a
oro =
  let result = V "result"
      a = V "a"
      b = V "b"
  in
  Let (def "oro" ["a", "b", "result"] $
    (a === falso &&& b === falso &&& result === falso) |||
    (a === falso &&& b === trueo &&& result === trueo) |||
    (a === trueo &&& b === falso &&& result === trueo) |||
    (a === trueo &&& b === trueo &&& result === trueo)
  )

ando :: G a -> G a
ando =
  let result = V "result"
      a = V "a"
      b = V "b"
  in
  Let (def "ando" ["a", "b", "result"] $
    (a === falso &&& b === falso &&& result === falso) |||
    (a === falso &&& b === trueo &&& result === falso) |||
    (a === trueo &&& b === falso &&& result === falso) |||
    (a === trueo &&& b === trueo &&& result === trueo)
  )

noto :: G a -> G a
noto =
  let result = V "result"
      a = V "a"
      b = V "b"
  in
  Let (def "noto" ["a", "result"] $
    (a === trueo&&& result === falso) |||
    (a === falso &&& result === trueo)
  )

loginto :: G a -> G a
loginto =
  let subst = V "subst"
      formula = V "formula"
      result = V "result"
  in
  Let (def "loginto" ["subst", "formula", "result"] $
  fresh ["x", "y", "l", "r", "rl", "rr"] (
      (formula === true &&& result === trueo)
  ||| (formula === false &&& result === falso)
  ||| (formula === var (V "y") &&& call "lookupo" [subst, V "y", result])
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
-- Logic interpreter Not-And basis.
--
-- Results are even worse.
--
logintoNotAnd :: G a -> G a
logintoNotAnd =
  let subst = V "subst"
      formula = V "formula"
      result = V "result"
  in
  Let (def "loginto" ["subst", "formula", "result"] $
  fresh ["x", "y", "l", "r", "rl", "rr"] (
      (formula === true &&& result === true)
  ||| (formula === false &&& result === false)
  ||| (formula === var (V "y") &&& call "lookupo" [subst, V "y", result])
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
       &&& call "oroNotAnd" [V "rl", V "rr", result])
  )) . lookupo . oroNotAnd . noto . ando
  where
    oroNotAnd :: G a -> G a
    oroNotAnd =
      Let (def "oroNotAnd" ["a", "b", "result"] $
        fresh ["x", "y", "z"] (
          call "noto" [V "x", V "result"] &&&
          call "ando" [V "y", V "z", V "x"] &&&
          call "noto" [V "a", V "y"] &&&
          call "noto" [V "b", V "z"]
      )) . noto . ando

--
-- Test formulas
--
logintoTest1 = loginto $ fresh ["s", "r"] $ call "loginto" [V "s", true, V "r"]
logintoTest2 = loginto $ fresh ["s", "r"] $ call "loginto" [V "s", false, V "r"]
logintoTest3 = loginto $ fresh ["s", "r"] $ call "loginto" [V "s", neg false, V "r"]
logintoTest4 = loginto $ fresh ["s", "r"] $ call "loginto" [V "s", conj true false, V "r"]
logintoTest5 = loginto $ fresh ["s", "r"] $ call "loginto" [V "s", disj true false, V "r"]
logintoTest6 = loginto $ fresh ["r", "x"] $ call "loginto" [(pair (C "x" []) true) % nil, var (C "x" []), V "rs"]
logintoTest7 = loginto $ fresh ["r", "x", "y"] $ call "loginto" [(pair (C "y" []) true) % nil, conj (V "x") (neg (var $ C "y" [])), V "r"]

--
-- Log expressions
--

varX = var (C "x" [])
varY = var (C "y" [])
varZ = var (C "z" [])

--
-- (x \/ y) /\ (\neg x \/ y)
--
logExpr1 = conj (disj varX varY) (disj (neg varX) varY)
logExpr2 = conj (conj (disj (conj varX (neg varY)) (conj (neg varX) varY)) varX) varY

logExpr3 = neg varX

-- (x || y)(x || z)(!y || z)(!y || x)
logExpr4 = conj (conj (conj (disj varX varY) (disj varX varZ)) (disj (neg varY) varX)) (disj (neg varY) varX)
subst4 = pair varX trueo % pair varY trueo % pair varZ trueo % nil

--
-- Test queries
--
logintoQuery6 = loginto $ fresh ["s", "x", "y"] $ call "loginto" [V "s", trueo, trueo]
logintoQuery5 = loginto $ fresh ["s", "x", "y"] $ call "loginto" [V "s", logExpr3, trueo]
logintoQuery1 = loginto $ fresh ["s", "f", "r"] $ call "loginto" [V "s", V "f", V "r"]
--
-- loginto st (x \/ y) /\ (\neg x \/ y) trueo -- найти подстановку, в которой выполняется формула
--
-- Это только x = true, y == true
logintoQuery2 = loginto $ fresh ["s", "f", "r", "x", "y"] $ call "loginto" [V "s", logExpr1, trueo]
logintoQuery3 = loginto $ fresh ["s", "f", "r", "x", "y"] $ call "loginto" [V "s", logExpr2, trueo]
logintoQuery4 = loginto $ fresh ["s", "f", "r"] $ call "loginto" [V "s", V "f", trueo]
logintoQuery7 = loginto $ fresh ["s"] $ call "loginto" [subst4, logExpr4, trueo]
