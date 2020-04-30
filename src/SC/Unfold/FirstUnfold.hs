module SC.Unfold.FirstUnfold where
    
import Syntax
import SC.DTree

import qualified Eval as E
import qualified Purification as P

import Utils

import Data.Function (on)
import Data.Maybe (mapMaybe, fromJust)
import Data.List
import qualified Data.Set as Set

import Text.Printf
import DotPrinter
import SC.SC

import Debug.Trace
import Control.Exception (assert)

trace' _ = id

newtype FstGoal = FstGoal DGoal deriving Show

instance UnfoldableGoal FstGoal where
  getGoal (FstGoal dgoal) = dgoal
  initGoal      = FstGoal     
  emptyGoal (FstGoal dgoal) = null dgoal
  mapGoal (FstGoal dgoal) f = FstGoal (f dgoal)
  unfoldStep = unreqUnfoldStep

unreqUnfoldStep (FstGoal dgoal) env subst cstore = let
    (ls, conj, rs) = splitGoal env dgoal
    (newEnv, uConj) = unfold conj env

    nConj = goalToDNF uConj
    unConj = unifyAll subst cstore nConj
    us = (\(cs, subst, cstore) -> (subst, cstore, suGoal subst cs ls rs)) <$> unConj
  in (us, newEnv)
  where
    suGoal subst cs ls rs = FstGoal $ E.substituteConjs subst $ ls ++ cs ++ rs

splitGoal :: E.Env -> DGoal -> ([G S], G S, [G S])
splitGoal env (g:gs) = ([], g, gs)
