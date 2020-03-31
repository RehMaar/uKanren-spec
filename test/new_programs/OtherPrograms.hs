module OtherPrograms where

import Syntax
import List as L

kmp :: G a -> G a
kmp =
  Let (def "kmp" ["pattern", "string"] $
    fresh ["l", "i", "r"] $
      call "appendo" [V "l", V "pattern", V "i"]
      &&& call "appendo" [V "i", V "r", V "string"]
  ) . L.appendo

kmpQuery pat str = kmp $ call "kmp" [pat, str]
kmpQuery1 = kmp $ fresh ["str"] $ call "kmp" [abba, V "str"]
  where abba = C "a" [] % C "b" [] % C "b" [] % C "a" []
