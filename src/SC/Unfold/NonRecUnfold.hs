module SC.Unfold.NonRecUnfold where
    
import Syntax
import SC.DTree

import qualified CPD.LocalControl as CPD
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

import Debug.Trace
import Control.Exception (assert)

trace' _ = id

data NUGoal = NUGoal DGoal deriving Show

topLevel :: G X -> (DTree, G S, [S])
topLevel g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  lgoal' = CPD.normalize lgoal
  igoal = assert (length lgoal' == 1) $ NUGoal (head lgoal')
  tree = fst3 $ derivationStep igoal Set.empty lgamma E.s0 Set.empty 0
  in (tree, lgoal, lnames)

instance UnfoldableGoal NUGoal where
  getGoal (NUGoal dgoal) = dgoal
  initGoal goal = NUGoal goal
  emptyGoal (NUGoal dgoal) = null dgoal
  mapGoal (NUGoal dgoal) f = NUGoal (f dgoal)


instance Unfold NUGoal where
  unfoldStep = unreqUnfoldStep

unreqUnfoldStep :: NUGoal -> E.Gamma -> E.Sigma -> ([(E.Sigma, NUGoal)], E.Gamma)
unreqUnfoldStep (NUGoal dgoal) env subst = let
    (conj, rest) = splitGoal env dgoal
    (newEnv, uConj) = unfold conj env

    nConj = goalToDNF uConj
    unConj = unifyAll subst nConj
    us = (\(cs, subst) -> (subst, suGoal subst cs rest)) <$> unConj
  in (us, newEnv)
  where
    suGoal subst cs rest = NUGoal $ E.substituteConjs subst $ cs ++ rest

splitGoal :: E.Gamma -> DGoal -> (G S, [G S])
splitGoal env gs = let (c:cs) = sortBy ((compare `on` (isRec env)) <>
                                        compareGoals env) gs
                    in (c, cs)

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
