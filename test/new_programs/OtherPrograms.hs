module OtherPrograms where

import Syntax
import List as L
import Num as N

matcher' :: G a -> G a
matcher' =
  Let (def "matcher" ["pattern", "string"] $
    fresh ["l", "i", "r"] $
      call "appendo" [V "l", V "pattern", V "i"]
      &&& call "appendo" [V "i", V "r", V "string"]
  ) . L.appendo

matcher =
  Let (def "matcher" ["pat", "str"] $
   call "matcher1" [V "pat", V "str", V "pat", V "str"]) .
  Let (def "matcher1" ["p1", "s1", "p2", "s2"] $
   (V "p1" === L.nil) |||
   fresh ["term", "tl", "dterm", "tl2", "d", "r"] (
     (V "p1" === (V "term") L.% (V "tl")   &&&
      V "s1" === (V "dterm") L.% (V "tl2") &&&
      V "s2" === (V "d") L.% (V "r")       &&&
      V "term" =/= V "dterm"               &&&
      call "matcher1" [V "p2", V "r", V "p2", V "r"]
     ) |||
     (V "p1" === (V "term") L.% (V "tl")   &&&
      V "s1" === (V "dterm") L.% (V "tl2") &&&
      call "matcher1" [V "tl", V "tl2", V "p2", V "s2"]
     )
   )
  )


matcherQuery pat str = matcher $ call "matcher" [pat, str]
matcherQuery1 = matcher $ fresh ["str"] $ call "matcher" [abba, V "str"]
  where abba = C "a" [] % C "b" [] % C "b" [] % C "a" []

matcherQuery2 = matcher $ call "matcher" [bb, abba]
  where abba = C "a" [] % C "b" [] % C "b" [] % C "a" []
        bb = C "a" []



eqNat =
  Let (def "eq" ["v1", "v2"] $
    (V "v1" === N.zero &&& V "v2" === N.zero) |||
    (fresh ["v11", "v22"]
    (V "v1" === N.suc (V "v11") &&& V "v2" === N.suc (V "v22")
    &&& call "eq" [V "v11", V "v22"]))
  )

eqNatQuerySame = eqNat $ fresh ["x"] $ call "eq" [V "x", V "x"]

