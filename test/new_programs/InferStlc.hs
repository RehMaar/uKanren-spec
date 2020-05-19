module InferStlc where

import Syntax
import qualified LamInt as Lam
import List

-- arrow type
arr x y = C "arr" [x, y]
-- primitive type
p x = C "p" [x]

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
       -- var =/= V "key" &&&
       call "lookupo" [V "tail", var, result]))
    )
  ))

infero1 :: G a -> G a
infero1 = Let (def "infero1" ["env", "expr", "type"] $
        fresh ["x"] (
          V "expr" === Lam.var (V "x") &&&
          call "lookupo" [V "env", V "x", V "type"]
        )
    ||| fresh ["lf", "rt", "t"] (
          V "expr" === Lam.app (V "lf") (V "rt") &&&
          call "infero1" [V "env", V "lf", arr (V "t") (V "type")] &&&
          call "infero1" [V "env", V "rt", (V "t")]
        )
    ||| fresh ["hd", "body", "lt", "rt"] (
          V "expr" === Lam.lam (V "hd") (V "body") &&&
          V "type" === arr (V "lt") (V "rt") &&&
          call "infero1" [Lam.pair (V "hd") (V "lt") % V "env", V "body", V "rt"]
        )
  ) . lookupo

infero :: G a -> G a
infero = Let (def "infero" ["expr", "type"] $ call "infero1" [nil, V "expr", V "type"]) . infero1

inferoEnv ="open GT\nopen OCanren\nopen Std\nopen Nat\nopen GLam\nopen GTyp"

-------------------------------------------------
-------------------------------------------------
-------------------------------------------------

varX = C "x" []
varY = C "y" []

inferoQuerySimple = infero $ fresh ["e", "t"] $ call "infero" [V "e", V "t"]

inferoQuery1 = infero $ fresh ["p"] $ call "infero" [expr1, V "p"]
  where
    expr1 = Lam.lam varX (Lam.var varX)

inferoQueryInhab1 = infero $ fresh ["e"] $ call "infero" [V "e", typ1]
  where
    typ1 = arr (p varX) (p varY)

-- ((((A -> B) -> A) -> A) -> B) -> B
weakPierce = arr (arr (arr (arr (arr (p a) (p b)) (p a)) (p a)) (p b)) (p b)
 where
   a = C "a" []
   b = C "b" []

inferoQueryPierce = infero $ fresh ["e"] $ call "infero" [V "e", weakPierce]

-- Term spec: (_ _) _
-- Type spec: _ -> (_ -> (p _))
termSpec = Lam.app (Lam.app (V "x") (V "y")) (V "z")
typeSpec = arr (V "a") (arr (V "b") (p (V "c")))

genBySpec = Let (def "genBySpec" ["expr", "type"] $
    fresh ["x", "y", "z", "a", "b", "c"] $
      V "expr" === termSpec &&&
      V "type" === typeSpec &&&
      call "infero" [V "expr", V "type"]
  ) . infero
genBySpecQuery = genBySpec $ fresh ["e", "t"] $ call "genBySpec" [V "e", V "t"]
