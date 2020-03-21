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

topLevel :: G X -> (DTree, G S, [S])
topLevel g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  lgoal' = normalize lgoal
  igoal = assert (length lgoal' == 1) $ FstGoal (head lgoal')
  tree = fst3 $ derivationStep igoal Set.empty lgamma E.s0 Set.empty 0
  in (tree, lgoal, lnames)

instance UnfoldableGoal FstGoal where
  getGoal (FstGoal dgoal) = dgoal
  initGoal      = FstGoal     
  emptyGoal (FstGoal dgoal) = null dgoal
  mapGoal (FstGoal dgoal) f = FstGoal (f dgoal)
  unfoldStep = unreqUnfoldStep


instance Unfold FstGoal where

unreqUnfoldStep :: FstGoal -> E.Gamma -> E.Sigma -> ([(E.Sigma, FstGoal)], E.Gamma)
unreqUnfoldStep (FstGoal dgoal) env subst = let
    (ls, conj, rs) = splitGoal env dgoal
    (newEnv, uConj) = unfold conj env

    nConj = goalToDNF uConj
    unConj = unifyAll subst nConj
    us = (\(cs, subst) -> (subst, suGoal subst cs ls rs)) <$> unConj
  in (us, newEnv)
  where
    suGoal subst cs ls rs = FstGoal $ E.substituteConjs subst $ ls ++ cs ++ rs

splitGoal :: E.Gamma -> DGoal -> ([G S], G S, [G S])
splitGoal env (g:gs) = ([], g, gs)

isRec :: E.Gamma -> G S -> Bool
isRec (p, _, _) goal@(Invoke call _) =
  let (name, args, body) = p call in
  any ((== name) . getInvokeName) $ getInvokes body
  where
    getInvokes b = concat $ filter isInvoke <$> normalize b
isRec _ _ = False

compareGoals :: E.Gamma -> G a -> G a -> Ordering
compareGoals (p, _, _) (Invoke g1 _) (Invoke g2 _)
  | g1 == g2
  = EQ
  | otherwise
  = let n1 = length $ normalize $ trd3 $ p g1
        n2 = length $ normalize $ trd3 $ p g2
    in compare n1 n2
compareGoals _ _ _ = EQ
