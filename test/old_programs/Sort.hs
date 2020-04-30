module Sort where

import Prelude hiding (succ, min, max)
import Syntax
import Bool
import Num
import List hiding (a, b)

minmaxo :: G a -> G a
minmaxo g =
  let a = V "a" in
  let b = V "b" in
  let min = V "min" in
  let max = V "max" in
  Let (
    def "minmaxo" ["a", "b", "min", "max"] (
      (min === a &&& max === b &&& call "leo" [a, b, trueo]) |||
      (max === a &&& min === b &&& call "gto" [a, b, trueo])
    )
  ) (leo $ gto g)

smallesto :: G a -> G a
smallesto g =
  let l = V "l" in
  let s = V "s" in
  let l' = V "l'" in
  let h = V "h" in
  let t = V "t" in
  let s' = V "s'" in
  let t' = V "t'" in
  let max = V "max" in
  Let (
    def "smallesto" ["l", "s", "l'"] (
      l === s % nil &&& l' === nil |||
      fresh ["h", "t", "s'", "t'", "max"] (
        l' === max % t' &&&
        l === h % t &&&
        call "minmaxo" [h, s', s, max] &&&
        call "smallesto" [t, s', t']
      )
    )
  ) $ minmaxo g

sorto :: G a -> G a
sorto g =
  let x = V "x" in
  let y = V "y" in
  let s = V "s" in
  let xs = V "xs" in
  let xs' = V "xs'" in
  Let (
    def "sorto" ["x", "y"] (
      x === nil &&& y === nil |||
      fresh ["s", "xs", "xs'"]
        ( y === s % xs'
             &&& call "smallesto" [x, s, xs]
             &&& call "sorto" [xs, xs']
        )
    )
  ) $ smallesto g
