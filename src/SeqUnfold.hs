module SeqUnfold where
    
import Syntax
import DTree

import qualified CPD
import qualified Eval as E
import qualified Purification as P
import qualified GlobalControl as GC

import Utils

import Data.Maybe (mapMaybe)
import Data.List
import qualified Data.Set as Set

import Text.Printf
import DotPrinter
import Unfold

import Debug.Trace

trace' _ = id

data SUGoal = SUGoal DGoal Int deriving Show

topLevel :: G X -> (DTree, G S, [S])
topLevel g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  igoal = SUGoal [lgoal] 0
  tree = fst3 $ derivationStep igoal Set.empty lgamma E.s0 Set.empty 0
  in (tree, lgoal, lnames)

instance Unfold SUGoal where
  getGoal (SUGoal dgoal _) = dgoal

  initGoal goal = SUGoal goal 0

  emptyGoal (SUGoal dgoal _) = null dgoal

  mapGoal (SUGoal dgoal idx) f = SUGoal (f dgoal) idx

  unfoldStep = seqUnfoldStep


seqUnfoldStep :: SUGoal -> E.Gamma -> E.Sigma -> ([(E.Sigma, SUGoal)], E.Gamma)
seqUnfoldStep (SUGoal dgoal idx) env subst = let
    (newIdx, (immut, conj, mut)) = splitGoal idx dgoal
    (newEnv, uConj) = unfold conj env

    nConj = goalToDNF uConj
    unConj = unifyAll subst nConj
    us = (\(cs, subst) -> (subst, suGoal subst immut cs mut newIdx)) <$> unConj
  in (us, newEnv)
  where
    suGoal subst immut cs mut newIdx = let
        goal = E.substituteConjs subst $ immut ++ cs ++ mut
      in SUGoal goal newIdx

splitGoal _ [g] = (0, ([], g, []))
splitGoal idx gs = let
  (ls, rs) = splitAt idx gs
  in case uncons rs of
      Just (c, []) -> (length ls, (ls, c, []))
      Just (c, rs) -> (succ idx, (ls, c, rs))
      Nothing -> splitGoal 0 gs
