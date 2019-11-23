module Test where

import System.Process (system)
import System.Exit (ExitCode)
import Data.Maybe
import Text.Printf

import Syntax
import DotPrinter
import SldTreePrinter
import GlobalTreePrinter
import Utils

import qualified CPD
import qualified CpdResidualization as CR
import qualified GlobalControl as GC
import qualified Purification as P
import qualified OCanrenize as OC

import qualified SeqUnfold as SU
import qualified FullUnfold as FU
import qualified RandUnfold as RU

import qualified DTree as DT
import qualified DTResidualize as DTR

import qualified LogicInt as LI
import qualified List as L
import qualified Sort as L
import qualified Num as L
import qualified Programs as L

import TestUtils

open g = openInPdf $ fst3 $ SU.topLevel g

cutTree = DTR.cutFailedDerivations . DTR.makeMarkedTree . fst3 . SU.topLevel
openCut = openInPdf . cutTree


testRevRev = L.reverso $ fresh ["xs", "sx"] $
  call "reverso" [V "xs", V "sx"] &&& call "reverso" [V "sx", V "xs"]

testRevRevRes = L.reverso $
  call "reverso" [list, listR] &&& call "reverso" [listR, list]
  where
    list = C "x" [] L.% C "y" [] L.% C "z" [] L.% L.nil
    listR = C "z" [] L.% C "y" [] L.% C "x" [] L.% L.nil

testMaxLen = L.maxLengtho $ fresh ["x", "m", "l"] $
  call "maxLengtho" [x, m, l]
  where
    x = V "x"
    m = V "m"
    l = V "l"

-- Test double appendo
testDA = L.doubleAppendo $ fresh ["a", "b", "c", "d"]
              (call "doubleAppendo" [V "a", V "b", V "c", V "d"])


-- Test double appendo
testDA1 = L.doubleAppendo $ fresh ["a", "b", "c", "d"]
              (call "doubleAppendo" [V "a", V "a", V "c", V "d"])


-- Test double appendo
testDA2 = L.doubleAppendo $ fresh ["a", "b", "c"]
              (call "doubleAppendo" [V "a", V "b", V "c", V "c"])


testDA3 = L.doubleAppendo $ fresh ["a", "b", "c", "d"]
              (call "doubleAppendo" [V "d", V "b", V "d", V "c"])

-- Test reverse without acc
testRev = L.reverso $ fresh ["a", "b"]
              (call "reverso" [V "a", V "b"])

-- Test reverse without acc'
testRev2 = L.reverso $ fresh ["a", "b"]
              (call "reverso" [L.peanify 1 L.% L.peanify 2 L.% L.peanify 3 L.% L.nil, V "b"])

-- Test reverse with acc
testRevac = L.revAcco $ fresh ["a", "b", "acc"]
              (call "revacco" [V "a", V "acc", V "b"])

-- Test reverse with acc (nil acc)
testRevac2 = L.revAcco $ fresh ["a", "b"]
              (call "revacco" [V "a", L.nil, V "b"])

testMaxo = L.maxo $ fresh ["a", "r"]
           (call "maxo" [V "a", V "r"])

testSort = L.sorto $ fresh ["xs", "ys"]
           (call "sorto" [V "xs", V "ys"])

testCall = outter $
  fresh ["x", "y", "z", "i"] $ call "outter" [V "x", V "y", V "z", V "i"]

outter :: G a -> G a
outter g =
  Let (def "outter" ["x", "y", "z", "i"] (call "g" [V "x", V "y"] &&& call "f" [V "z", V "i"])) $ gfun $ ffun g

gfun :: G a -> G a
gfun g =
  Let (def "g" ["x", "y"] (V "x" === L.nil ||| (call "listo" [V "y"]))) $ L.listo g

ffun :: G a -> G a
ffun g = Let (def "f" ["x", "y"] (call "listo" [V "x"])) $ L.listo g