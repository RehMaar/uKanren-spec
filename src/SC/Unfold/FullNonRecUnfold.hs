{- TODO: examples for this heuristics. -}
module SC.Unfold.FullNonRecUnfold where
        
import Syntax
import SC.DTree

import qualified Eval as E
import qualified Purification as P

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

instance UnfoldableGoal FullNUGoal where
  getGoal (FullNUGoal dgoal) = dgoal
  initGoal goal = FullNUGoal goal
  emptyGoal (FullNUGoal dgoal) = null dgoal
  mapGoal (FullNUGoal dgoal) f = FullNUGoal (f dgoal)
  unfoldStep = fnrUnfoldStep

fnrUnfoldStep (FullNUGoal dgoal) env subst cstore = let
    (ls, conj, rs) = splitGoal env dgoal
    (newEnv, uConj) = FU.unfoldAll env conj

    nConj = conjOfDNFtoDNF (goalToDNF <$> uConj)
    unConj = unifyAll subst cstore nConj
    us = (\(cs, subst, cstore) -> (subst, cstore, suGoal subst cs ls rs)) <$> unConj
  in (us, newEnv)
  where
    suGoal subst cs ls rs = FullNUGoal $ E.substituteConjs subst $ ls ++ cs ++ rs

splitGoal :: E.Env -> DGoal -> ([G S], [G S], [G S])
splitGoal env gs =
  case partition (not . isRec env) gs of
     ([], r) -> let (ls, g, rs) = NU.splitGoal env r in (ls, [g], rs)
     ((n:ns), r) -> (ns, [n], r)
