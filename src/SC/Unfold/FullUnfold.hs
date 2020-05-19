module SC.Unfold.FullUnfold where

import SC.DTree
import Syntax
import Utils

import qualified Eval as E
import Data.Maybe (mapMaybe)
import Data.List (group, sort)
import qualified Data.Set as Set
import Data.Tuple (swap)
import Data.Foldable (foldl')

import Text.Printf
import DotPrinter
import SC.SC

import Debug.Trace

newtype FUGoal = FUGoal DGoal deriving (Show, Eq, Ord)

instance UnfoldableGoal FUGoal where
  getGoal (FUGoal dgoal) = dgoal
  initGoal = FUGoal
  emptyGoal (FUGoal dgoal) = null dgoal
  mapGoal (FUGoal dgoal) f = FUGoal (f dgoal)
  unfoldStep = fullUnfoldStep

fullUnfoldStep (FUGoal goal) env subst cstore = let
    (newEnv, unfoldedGoal) = unfoldAll env goal
    n = (goalToDNF <$> unfoldedGoal)
    -- Goal :: [DNF of each body] :: [Body DNF [[Conj]]]
    normalizedGoal = conjOfDNFtoDNF n
    conjs = unifyAll subst cstore normalizedGoal
    -- Goal :: [Unified DNF] :: [Body DNF [[Conj] and Substs]]
    unifiedGoal = (\(conj, subst, cstore) -> (subst, cstore, FUGoal $ E.substituteConjs subst conj)) <$> conjs
  in (unifiedGoal, newEnv)

-- Return value is Conj (G S), but now (G S) is a body of corresponding Invoke.
--unfoldAll :: E.Env -> Conj (G S) -> (E.Env, Conj (G S))
--unfoldAll env = foldl' unfold' (env, [])
  --where
    --unfold' (env, goals) inv = (:goals) <$> unfold inv env

showUnified :: Disj (E.Subst, Conj (G S)) -> String
showUnified = concatMap (\(subst, conj) -> "(" ++ show (null subst) ++ ", " ++ show conj ++ ")")
