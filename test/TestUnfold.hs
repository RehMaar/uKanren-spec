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
import qualified LamInt as Lam
import qualified InferStlc as Infer

import qualified Bool as B
import qualified Num as N
import qualified Path
import qualified Unify
import qualified List

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

testD1 =
  all id
  [
  U.disunify es [] (V 1) (V 2)                           == Just [(1, V 2)],
  U.disunify es [] (C "S" []) (C "S" [])                 == Nothing,
  -- due to occurCheck this will never be unified
  U.disunify es [] (V 1) (C "S" [V 1])                   == Just [],
  -- TODO: the problem: for constructor we need at least one disunify, not all of them.
  -- for more proper results maybe we need save terms to constraits store, not
  -- just substitution.
  U.disunify es [] (C "S" [V 1, V 3]) (C "S" [V 4, V 2]) == Just [(2, V 3), (1, V 4)]
  ]
  where
    es = [] :: E.Subst

testVCS =
  all id
  [
  U.verifyCS s1 c1 == Nothing,
  U.verifyCS s1 c2 == Nothing,
  U.verifyCS s1 s2 == Just [(1, C "S" [V 2])],
  U.verifyCS s2 c3 == Just [(1, C "S" [C "Z" []]), (2, C "Z" [])]
  ]
  where
   s1 = [(1, V 2)]
   s2 = [(1, C "S" [V 2])]
   c1 = [(1, V 2)]
   c2 = [(2, V 1)]
   c3 = [(1, C "S" [C "Z" []])]


testUG =
  all id
  [
   U.unifyGoal s1 c1 g1 == Just ([Invoke "a" [V 1, V 2]], [], [(1, V 2)]),
   U.unifyGoal s1 c1 g2 == Nothing,
   U.unifyGoal s1 c1 g3 == Just ([], [(1, V 3), (0, V 3)], [(1, V 2), (2, V 3)])
  ]
  where
    s1 = []
    c1 = []
    g1 = [V 1 :#: V 2, Invoke "a" [V 1, V 2]]
    g2 = [V 1 :#: V 2, V 1 :=: V 2]
    g3 = [V 1 :#: V 2, C "S" [V 0, V 1] :=: C "S" [V 3, V 0]]


------------------------------------------
-- Test unfold methods
------------------------------------------

-- pathPrefix :: String
-- pathPrefix = "test/ocanren/auto/"

toTestPath pathPrefix fpath (n:name) = pathPrefix ++ fromMaybe "" fpath ++ toUpper n : name ++ ".ml"

data TestMethod = TM { tmName :: String, tmFun :: U.SuperComp}

data TestQuery = TQ { tqName :: String, tqQuery :: G X, env :: Maybe String, tmDir :: Maybe String}

methods runner =
  [
    --TM "ranu" (RU.topLevel 17),
      TM "sequ" (runner "SU")
    , TM "nrcu" (runner "NU")
    , TM "recu" (runner "RU")
    , TM "minu" (runner "MnU")
    , TM "maxu" (runner "MxU")
    , TM "fstu" (runner "FstU")
    , TM "fulu" (runner "FU")
    , TM "fnu"  (runner "FnU")
  ]

methods1 =  ("SC1", methods SCI.run1)
methods2 =  ("SC2", methods SCI.run2)
methods3 =  ("SC3", methods SCI.run3)
methodsU =  ("SCU", methods SCI.runU)
methodsU2 = ("SCU2", methods SCI.runU2)
methodsU3 = ("SCU3", methods SCI.runU3)

-- reverso(a, a)
palindromeTQ = TQ "Pldrm" testRev' Nothing (Just "pldrmAuto/src/")
-- doubleAppend(a, b, c, d)
dappTQ = TQ "Dapp" testDA Nothing (Just "dappAuto/src/")
revTQ = TQ "Rev" testReversoSame Nothing (Just "dappAuto/src/")
-- loginto(form, subst, true)
-- TODO: bug residualize: for FstU SCU2
logintTQ = TQ "Logint" LI.logintoQueryTrue (Just LI.logintoEnv) (Just "logintAuto/src/")

lamTQ = TQ "Lam" Lam.slamoQueryId (Just Lam.slamoEnv) (Just "lam/src/")
quineTQ = TQ "Quine" Lam.slamoQueryQuine (Just Lam.slamoEnv) (Just "quines/src/")

inferTQ = TQ "Infer" Infer.inferoQuerySimple (Just Infer.inferoEnv) (Just "inferAuto/src/")

genSpecTQ = TQ "Infer" Infer.genBySpecQuery (Just Infer.inferoEnv) (Just "inferAuto/src/")

-- maxLengtho(..)
maxlenTQ = TQ "MaxLen" testMaxLen Nothing (Just "maxLenAuto/src/")
-- isPath(graph, path, true)
isPathTQ = TQ "IsPath" Path.query1 Nothing (Just "pathAuto/src/")

isPathLenTQ = TQ "IsPathOfLength" pathLenQuery Nothing (Just "pathAuto/src/")

pathLenQuery = pathLen $ fresh ["p", "g"] $ call "pathLen" [V "p", V "g"]
  where
    pathLen = Let (def "pathLen" ["p", "g"]
      (call "isPath" [V "p", V "g", B.trueo] &&& call "lengtho" [N.peanify 1, V "p"])
      ) . Path.path . List.lengtho
-- 
unifyTQ  = TQ "Unify" Unify.query (Just env) (Just "unifyAuto/src/")
  where env = "open OCanren\nopen GT\nopen Std\nopen Nat\nopen UnifyTerm\n"
-- Simple sorting
sortTQ = TQ "Sort" testSort Nothing (Just "sortAuto/src/")
-- Lam Quine
--red2StepTQ = TQ "Red2Step" LamInt.slamoQueryRes2Step Nothing (Just "lamRed2/src")


testMethodsOnTest1 query  = mapM_ (testMethodOnTest "test/ocanren/auto/" query) $ snd methods1
testMethodsOnTest2 query  = mapM_ (testMethodOnTest "test/ocanren/auto/" query) $ snd methods2
testMethodsOnTest3 query  = mapM_ (testMethodOnTest "test/ocanren/auto/" query) $ snd methods3
testMethodsOnTestU query  = mapM_ (testMethodOnTest "test/ocanren/auto/" query) $ snd methodsU
testMethodsOnTestU2 query = mapM_ (testMethodOnTest "test/ocanren/auto/" query) $ snd methodsU2
testMethodsOnTestU3 query = mapM_ (testMethodOnTest "test/ocanren/auto/" query) $ snd methodsU3

testMethodOnTest prefix (TQ qname query env path) (TM fname fun) = do
   putStrLn $ "Query: " ++ qname ++ " Method: " ++ fname
   let testPath = toTestPath prefix path $ fname ++ qname
   TestUtils.ocanrenUltraGen env fun (fname ++ qname) testPath query



testMethodsOnTest1' query  = mapM_ (testMethodOnTest' "test/ocanren/auto/" (fst methods1) query) $ snd methods1
testMethodsOnTest2' query  = mapM_ (testMethodOnTest' "test/ocanren/auto/" (fst methods2) query) $ snd methods2
testMethodsOnTest3' query  = mapM_ (testMethodOnTest' "test/ocanren/auto/" (fst methods3) query) $ snd methods3
testMethodsOnTestU' query  = mapM_ (testMethodOnTest' "test/ocanren/auto/" (fst methodsU) query) $ snd methodsU
testMethodsOnTestU2' query = mapM_ (testMethodOnTest' "test/ocanren/auto/" (fst methodsU2) query) $ snd methodsU2
testMethodsOnTestU3' query = mapM_ (testMethodOnTest' "test/ocanren/auto/" (fst methodsU3) query) $ snd methodsU3


testMethodOnTest' prefix methodPrefix (TQ qname query env path) (TM fname fun) = do
   putStrLn $ "Query: " ++ qname ++ " Method: " ++ fname
   let testPath = toTestPath prefix path $ fname ++ qname ++ methodPrefix
   TestUtils.ocanrenUltraGen env fun (fname ++ qname ++ methodPrefix) testPath query

testAllMethods query = mapM_ (\f -> f query) [testMethodsOnTest1', testMethodsOnTest2', testMethodsOnTest3', testMethodsOnTestU', testMethodsOnTestU2', testMethodsOnTest3']

testMethodOnTestQuick (TQ qname query env _) (TM fname fun) = do
   TestUtils.ocanrenUltraGen env fun (fname ++ qname) (fname ++ qname ++ ".ml") query

lenQ = List.lengtho $ fresh ["p"] $ call "lengtho" [V "p", N.suc N.zero]

---------------------------------------------------------
---------------------------------------------------------
---------------------------------------------------------
---------------------------------------------------------
--
-- Test queries
--
--
---------------------------------------------------------

-- specialize (doubleAppend list1 list2 list3 result)
testDoubleAppendo = testDA

-- specialize (reverso list result)
testReverso = testRev
-- specialize (reverso list list)
testReversoSame = testRev'

-- specialize (maxLengtho list max length)
testMaxLengtho = testMaxLen

