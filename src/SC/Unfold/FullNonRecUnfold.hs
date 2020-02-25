{- TODO: examples for this heuristics. -}
module SC.Unfold.FullNonRecUnfold where
        
import Syntax
import SC.DTree

import qualified CPD.LocalControl as CPD
import qualified Eval as E
import qualified Purification as P
import qualified CPD.GlobalControl as GC

import Utils

import Data.Function (on)
import Data.Maybe (mapMaybe)
import Data.List
import qualified Data.Set as Set

import Text.Printf
import DotPrinter
import SC.SC
import qualified SC.Unfold.FullUnfold as FU
import qualified SC.Unfold.NonRecUnfold as NU

import Debug.Trace
import Control.Exception (assert)

trace' _ = id

data FullNUGoal = FullNUGoal DGoal deriving Show

topLevel :: G X -> (DTree, G S, [S])
topLevel g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  lgoal' = CPD.normalize lgoal
  igoal = assert (length lgoal' == 1) $ FullNUGoal (head lgoal')
  tree = fst3 $ derivationStep igoal Set.empty lgamma E.s0 Set.empty 0
  in (tree, lgoal, lnames)

instance UnfoldableGoal FullNUGoal where
  getGoal (FullNUGoal dgoal) = dgoal
  initGoal goal = FullNUGoal goal
  emptyGoal (FullNUGoal dgoal) = null dgoal
  mapGoal (FullNUGoal dgoal) f = FullNUGoal (f dgoal)


instance Unfold FullNUGoal where
  unfoldStep = fnrUnfoldStep

fnrUnfoldStep :: FullNUGoal -> E.Gamma -> E.Sigma -> ([(E.Sigma, FullNUGoal)], E.Gamma)
fnrUnfoldStep (FullNUGoal dgoal) env subst = let
    (conj, rest) = splitGoal env dgoal
    (newEnv, uConj) = FU.unfoldAll env conj

    nConj = conjOfDNFtoDNF (goalToDNF <$> uConj)
    unConj = unifyAll subst nConj
    us = (\(cs, subst) -> (subst, suGoal subst cs rest)) <$> unConj
  in (us, newEnv)
  where
    suGoal subst cs rest = FullNUGoal $ E.substituteConjs subst $ cs ++ rest

splitGoal :: E.Gamma -> DGoal -> ([G S], [G S])
splitGoal env gs =
  case partition (not . NU.isRec env) gs of
     ([], r) -> let (g, gs) = NU.splitGoal env r in ([g], gs)
     (n, r) -> (n, r)
