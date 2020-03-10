module TestUnfold where

import Syntax
import qualified Eval as E
import qualified SC.Unfold.SeqUnfold as SU
import qualified SC.Unfold.FullUnfold as FU
import qualified SC.Unfold.RandUnfold as RU
import qualified SC.Unfold.RecUnfold as RecU
import qualified SC.Unfold.NonRecUnfold as NU
import qualified SC.Unfold.MaxUnfold as MaxU
import qualified SC.Unfold.MinUnfold as MinU

import qualified SC.SC as U
import qualified SC.SCInst as SCI
import qualified SC.DTResidualize as DTR
import SC.DTree
import Utils

import qualified LogicInt as LI

import qualified Num as N
import qualified Path
import qualified Unify

-- import System.Directory

import TestUtils
import Test

import Data.List
import Data.Char (toUpper)
import Data.Monoid (First(..), getFirst)
import Data.Maybe (fromMaybe)

------------------------------------------
-- Run tests of utils functions
------------------------------------------
runTests = all id [testFlatConj
                  , testGetVarFromTerm
                  , testGenLetSig
                  ]

-------------------------------------------
-- Test utls
------------------------------------------
testFlatConj = all id [testFlatConjOfDNF1, testFlatConjOfDNF2, testFlatConjOfDNF3]
  where
    t1 :: [[[String]]]
    t1 = []
    t1r = []
    t2 :: [[[String]]]
    t2 = [[["a", "b"], ["c", "d"]]]
    t2r = [["a", "b"], ["c", "d"]]
    t3 = [[["a", "b"], ["c", "d"]], [["e", "f"], ["g", "h"]]]
    t3r = [["a", "b", "e", "f"], ["c", "d", "e", "f"], ["a", "b", "g", "h"], ["c", "d", "g", "h"]]
    t4 = [[["a", "b"], ["c", "d", "e"]], [["f", "g", "h"], ["i", "j", "k"], ["l", "m"]], [["n", "o", "p"]]]

    testFlatConjOfDNF1 = U.conjOfDNFtoDNF t1 == t1r
    testFlatConjOfDNF2 = U.conjOfDNFtoDNF t2 == t2r
    testFlatConjOfDNF3 = (sort $ sort <$> U.conjOfDNFtoDNF t3) == (sort $ sort <$> t3r)


testGetVarFromTerm = all id [test1, test2, test3, test4, test5]
  where
    test1 = DTR.getVarFromTerm (V 0) == [V 0]
    test2 = null $ DTR.getVarFromTerm (C "_" [])
    test3 = null $ DTR.getVarFromTerm (N.peanify 10)
    test4 = DTR.getVarFromTerm (C "S" [C "S" [V 0]]) == [V 0]
    test5 = DTR.getVarFromTerm (C "_" [V 0, V 1, C "_" [V 2, V 3]]) == [V 0, V 1, V 2, V 3]

testGenLetSig = all id [test1, test2, test3]
  where
    test1 = DTR.genLetSig [Invoke "test" [V 0, V 1]] == ("test", [V 0, V 1])
    test2 = DTR.genLetSig [Invoke "test" [C "S" [C "O" []]]] == ("test", [] :: [Term X])
    test3 = DTR.genLetSig [Invoke "test" [V 0, C "S" [C "O" []], V 2]] == ("test", [V 0, V 2])

testMWL = DTR.mapTwoLists [1, 2, 2] [1, 2, 3] == Nothing
       && DTR.mapTwoLists [] [] == Just ([] :: [(S, S)])
       && DTR.mapTwoLists [1] [1] == Just [(1, 1)]
       && DTR.mapTwoLists [1] [2] == Just [(1, 2)]
       && DTR.mapTwoLists [1, 2] [2, 5] == Just [(1, 2), (2, 5)]

------------------------------------------
-- Test unfold methods
------------------------------------------

pathPrefix :: String
pathPrefix = "test/ocanren/auto/"

toTestPath fpath (n:name) = pathPrefix ++ fromMaybe "" fpath ++ toUpper n : name ++ ".ml"

data TestMethod = TM { tmName :: String, tmFun :: U.SuperComp}

data TestQuery = TQ { tqName :: String, tqQuery :: G X, env :: Maybe String, tmDir :: Maybe String}

methods runner =
  [
    --TM "ranu" (RU.topLevel 17),
    TM "fulu" (runner "FU"),
    TM "sequ" (runner "SU"),
    TM "nrcu" (runner "NU"),
    TM "recu" (runner "RU"),
    TM "minu" (runner "MnU"),
    TM "maxu" (runner "MxU"),
    TM "fstu" (runner "FstU")
  ]

methods1 = methods SCI.run1
methods2 = methods SCI.run2

dappTQ = TQ "Dapp" testDA Nothing (Just "dappAuto/src/")
logintTQ = TQ "Logint" LI.logintoQueryTrue (Just LI.logintoEnv) (Just "logintAuto/src/")
maxlenTQ = TQ "MaxLen" testMaxLen Nothing (Just "maxLenAuto/src/")
isPathTQ = TQ "IsPath" Path.query1 Nothing (Just "pathAuto/src/")
unifyTQ  = TQ "Unify" Unify.query (Just env) (Just "unifyAuto/src/")
  where
    env = "open OCanren\nopen GT\nopen Std\nopen Nat\nopen UnifyTerm\n"

testMethodsOnTest1 query = mapM_ (testMethodOnTest query) methods1
testMethodsOnTest2 query = mapM_ (testMethodOnTest query) methods2

testMethodOnTest (TQ qname query env path) (TM fname fun) = do
   putStrLn $ "Query: " ++ qname ++ " Method: " ++ fname
   TestUtils.ocanrenUltraGen env fun (fname ++ qname) (toTestPath path $ fname ++ qname) query

testMethodOnTestQuick (TQ qname query env _) (TM fname fun) = do
   TestUtils.ocanrenUltraGen env fun (fname ++ qname) (fname ++ qname ++ ".ml") query
