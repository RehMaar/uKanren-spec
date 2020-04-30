module SchemeInt where

import Syntax
import List
import Num

pair x y = C "pair" [x, y]

not_in_env :: G a -> G a
not_in_env = Let (def "not_in_env" ["x", "env"] $
    (V "env" === nil) |||
    (fresh ["y", "v", "rest"]
      (V "env" === pair (V "y") (V "v") % V "rest") &&&
      (V "y" =/= V "x") &&&
      call "not_in_env" [V "x", V "rest"])
  )

lookupo :: G a -> G a
lookupo = Let (def "lookupo" ["x", "env", "t"] $
    fresh ["y", "v", "rest"] $
    ((V "y" === V "x") &&& (V "env" === pair (V "y") (V "v") % V "rest")) |||
    ((V "y" =/= V "x") &&& (V "env" === pair (V "y") (V "v") % V "rest")
     &&& call "lookupo" [V "x", V "rest", V "t"]))

{-
(closure args

'((lambda (y) (lambda (z) z)) )



-}

app l r = C "app" [l, r]
closure x body env = C "closure" [x, body, env]
lam x body = C "lam" [x, body]
var x = C "var" [x]

schemeint' :: G a -> G a
schemeint' = Let (def "eval'" ["expr", "env", "val"] $
  (fresh ["rator", "rand", "x", "body", "env'", "a"] $
    (V "expr"  === app (V "rator") (V "rand") &&&
    call "eval'" [V "rator", V "env", closure (V "x") (V "body") (V "env'")] &&&
    call "eval'" [V "rand" , V "env", V "a"] &&&
    call "eval'" [V "body" , pair (V "x") (V "a") % V "env'", V "val"]) |||
  (fresh ["x", "body"] $
    (V "expr" === lam (var (V "x")) (V "body")) &&&
    (V "val" === closure (V "x") (V "body") (V "env"))
    -- (not-in-env 'lambda env) what does it mean?
  ) |||
  (fresh ["v"] $
     V "expr" === var (V "v") &&&
     call "lookupo" [V "v", V "env", V "val"]
  )))

schemeint :: G a -> G a
schemeint = Let $ def "eval" ["term", "val"] $ call "eval'" [V "term", nil, V "val"]
