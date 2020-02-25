module SC.Unfold.MaxUnfold where
    
import Syntax
import SC.DTree

import qualified CPD.LocalControl as CPD
import qualified Eval as E
import qualified Purification as P

import Utils

import Data.Maybe (mapMaybe)
import Data.List
import Data.Function (on)
import qualified Data.Set as Set


import Text.Printf
import DotPrinter
import SC.SC

import Debug.Trace
import Control.Exception (assert)

trace' _ = id

data MaxGoal = MaxGoal DGoal deriving Show

topLevel :: G X -> (DTree, G S, [S])
topLevel g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  lgoal' = CPD.normalize lgoal
  igoal = assert (length lgoal' == 1) $ MaxGoal (head lgoal')
  tree = fst3 $ derivationStep igoal Set.empty lgamma E.s0 Set.empty 0
  in (tree, lgoal, lnames)

instance UnfoldableGoal MaxGoal where
  getGoal (MaxGoal dgoal) = dgoal
  initGoal goal = MaxGoal goal
  emptyGoal (MaxGoal dgoal) = null dgoal
  mapGoal (MaxGoal dgoal) f = MaxGoal (f dgoal)


instance Unfold MaxGoal where
  unfoldStep = genUnfoldStep splitGoal MaxGoal

splitGoal :: E.Gamma -> MaxGoal -> (G S, DGoal)
splitGoal env (MaxGoal gs) = let (c:cs) = sortBy (compareGoals env) gs
                    in (c, cs)

compareGoals :: E.Gamma -> G a -> G a -> Ordering
compareGoals (p, _, _) (Invoke g1 _) (Invoke g2 _)
  | g1 == g2
  = EQ
  | otherwise
  = let n1 = length $ normalize $ trd3 $ p g1
        n2 = length $ normalize $ trd3 $ p g2
    in compare n2 n1
compareGoals _ _ _ = EQ
