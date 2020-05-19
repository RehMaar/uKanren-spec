module SchemeInt where

import Syntax
import List
import Num

import Data.List (intercalate)
import qualified Purification as P

pair x y = C "pair" [x, y]

not_in_env :: G a -> G a
not_in_env = Let (def "not_in_env" ["x", "env"] $
    (V "env" === nil) |||
    (fresh ["y", "v", "rest"] $
      (V "env" === pair (V "y") (V "v") % V "rest") &&&
      (V "y" =/= V "x") &&&
      call "not_in_env" [V "x", V "rest"])
  )

lookupo :: G a -> G a
lookupo = Let (def "lookupo" ["x", "env", "t"] $
    fresh ["y", "v", "rest"] $
    ((V "y" === V "x") &&& (V "env" === pair (V "y") (V "t") % V "rest")) |||
    ((V "y" =/= V "x") &&& (V "env" === pair (V "y") (V "v") % V "rest")
     &&& call "lookupo" [V "x", V "rest", V "t"]))

siLookupQuery1 = lookupo $ fresh ["x", "env", "t"] $ call "lookupo" [V "x", V "env", V "t"]

app l r = C "app" [l, r]
closure x body env = C "closure" [x, body, env]
lam x body = C "lam" [x, body]
symb x = C "symb" [x]

{- Translation of faster-miniKanren/simple-interp.scm -}
schemeint' :: G a -> G a
schemeint' = Let (def "eval_env" ["expr", "env", "val"] $
  (fresh ["rator", "rand", "x", "body", "env'", "a"] $
    (V "expr"  === app (V "rator") (V "rand") &&&
    call "eval_env" [V "rator", V "env", closure (V "x") (V "body") (V "env'")] &&&
    call "eval_env" [V "rand" , V "env", V "a"] &&&
    call "eval_env" [V "body" , pair (V "x") (V "a") % V "env'", V "val"]) |||
  (fresh ["x", "body"] $
    (V "expr" === lam (symb (V "x")) (V "body")) &&&
    (V "val" === closure (V "x") (V "body") (V "env"))
    &&& call "not_in_env" [C "lam" [], V "env"]
  ) |||
  (fresh ["v"] $
     V "expr" === symb (V "v") &&&
     call "lookupo" [V "v", V "env", V "val"]
  ))) . lookupo . not_in_env

schemeint :: G a -> G a
schemeint = Let (def "eval" ["term", "val"] $ call "eval_env" [V "term", nil, V "val"]) . schemeint'

siQueryId = schemeint $ fresh ["t", "v"] $ call "eval" [V "t", V "v"]
siQueryQuine = schemeint $ fresh ["t", "t"] $ call "eval" [V "t", V "t"]


----------------------------

{-
eval =
  Let (def "eval" ["term", "env", "val"] $
     fresh ["x"] (
        (V "term" === ident (V "x")) &&&
        call "lookupo" [V "x", V "env", V "val"]
     ) |||
     fresh ["t", "ts"] (
        (V "term" === seq (V "t" % V "ts")) &&& (
			    fresh ["id"] (
			       (V "t" === ident "id") &&& (
			       (V "id" === lambda &&& call "lambdaH" [V "ts", V "env", V "val"]) |||
			       (V "id" === quote  &&& call "quoteH" [V "ts", V "env", V "val"]) |||
			       (V "id" === list   &&& call "listH" [V "ts", V "env", V "val"]) |||
    		  	 ))
          ) |||
          fresh ["s", "arg", "val1", "x", "body", "env'", "val2"] (
            (V "t" === seq (V "s")) &&&
            (V "ts" === V "arg" % nil) &&&
            (V "val1" === closure (V "x") (V "body") (V "env'")) &&&
					  call "eval" [V "t", V "env", V "val1"] &&&
					  call "eval" [V "arg", V "env", v "val2"] &&&
					  call "eval" [V "body", (pair (V "x") (V "val2") % V "env'" , V "val"]
          )
        )
     )
  ) . lookupo . lambdaH . quoteH . listH

lambdaH =
  Let (def "lambdaH" ["ts", "env", "res"]
		call "not_in_env" [lambda, V "env"] &&&

  )
-}
