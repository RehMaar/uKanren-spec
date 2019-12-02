module Unfold.FullUnfold where

import DTree
import Syntax
import Utils

import qualified CPD
import qualified Eval as E
import qualified GlobalControl as GC


import Data.Maybe (mapMaybe)
import Data.List (group, sort)
import qualified Data.Set as Set
import Data.Tuple (swap)

import Text.Printf
import DotPrinter
import Unfold.Unfold

import Debug.Trace

newtype FUGoal = FUGoal DGoal deriving Show

topLevel :: G X -> (DTree, G S, [S])
topLevel g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  igoal = FUGoal [lgoal]
  tree = fst3 $ derivationStep igoal Set.empty lgamma E.s0 Set.empty 0
  in (tree, lgoal, lnames)

instance Unfold FUGoal where
  getGoal (FUGoal dgoal) = dgoal

  initGoal = FUGoal

  emptyGoal (FUGoal dgoal) = null dgoal

  mapGoal (FUGoal dgoal) f = FUGoal (f dgoal)

  unfoldStep = fullUnfoldStep
    where
      fullUnfoldStep :: FUGoal  -> E.Gamma -> E.Sigma -> ([(E.Sigma, FUGoal)], E.Gamma)
      fullUnfoldStep (FUGoal goal) env subst = let
          (newEnv, unfoldedGoal) = unfoldAll env goal
          n = (goalToDNF <$> unfoldedGoal)
          -- Goal :: [DNF of each body] :: [Body DNF [[Conj]]]
          normalizedGoal = conjOfDNFtoDNF n
          -- Goal :: [Unified DNF] :: [Body DNF [[Conj] and Substs]]
          unifiedGoal = (\(conj, subst) -> (subst, FUGoal $ E.substituteConjs subst conj)) <$> unifyAll subst normalizedGoal
        in (unifiedGoal, newEnv)

-- Return value is Conj (G S), but now (G S) is a body of corresponding Invoke.
unfoldAll :: E.Gamma -> Conj (G S) -> (E.Gamma, Conj (G S))
unfoldAll gamma = foldl unfold' (gamma, [])
  where
    unfold' (gamma, goals) inv = (:goals) <$> unfold inv gamma

showUnified :: Disj (E.Sigma, Conj (G S)) -> String
showUnified = concatMap (\(subst, conj) -> "(" ++ show (null subst) ++ ", " ++ show conj ++ ")")
