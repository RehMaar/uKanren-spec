module SC.Unfold.MinUnfold where
    
import Syntax
import SC.DTree

import qualified Eval as E
import qualified Purification as P

import Utils

import Data.Maybe (mapMaybe, fromJust)
import Data.List
import Data.Function (on)
import qualified Data.Set as Set


import Text.Printf
import DotPrinter
import SC.SC

import Debug.Trace
import Control.Exception (assert)

trace' _ = id

newtype MinGoal = MinGoal DGoal deriving Show

topLevel :: G X -> (DTree, G S, [S])
topLevel g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  lgoal' = normalize lgoal
  igoal = assert (length lgoal' == 1) $ MinGoal (head lgoal')
  tree = fst3 $ derivationStep igoal Set.empty lgamma E.s0 Set.empty 0
  in (tree, lgoal, lnames)

instance UnfoldableGoal MinGoal where
  getGoal (MinGoal dgoal) = dgoal
  initGoal = MinGoal
  emptyGoal (MinGoal dgoal) = null dgoal
  mapGoal (MinGoal dgoal) f = MinGoal (f dgoal)
  unfoldStep = genUnfoldStep splitGoal MinGoal


instance Unfold MinGoal where

--splitGoal :: E.Gamma -> MinGoal -> (G S, DGoal)
--splitGoal env (MinGoal gs) = let (c:cs) = sortBy (compareGoals env) gs
--                    in (c, cs)

splitGoal :: E.Gamma -> MinGoal -> (DGoal, G S, DGoal)
splitGoal env (MinGoal gs) =
  let c = minimumBy (compareGoals env) gs
  in fromJust $ split (c ==) gs

compareGoals :: E.Gamma -> G a -> G a -> Ordering
compareGoals (p, _, _) (Invoke g1 _) (Invoke g2 _)
  | g1 == g2
  = EQ
  | otherwise
  = let n1 = length $ normalize $ trd3 $ p g1
        n2 = length $ normalize $ trd3 $ p g2
    in compare n1 n2
compareGoals _ _ _ = EQ
