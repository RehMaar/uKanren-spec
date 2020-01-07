module TestUnfold where

import Syntax
import qualified Unfold.Unfold as U
import qualified DTResidualize as DTR

import qualified Num as N

import Data.List

runTests = all id [testFlatConj
                  , testGetVarFromTerm
                  , testGenLetSig
                  ]

--
-- Tests
--

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
