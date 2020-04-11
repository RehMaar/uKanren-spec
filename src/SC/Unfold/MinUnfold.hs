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

instance UnfoldableGoal MinGoal where
  getGoal (MinGoal dgoal) = dgoal
  initGoal = MinGoal
  emptyGoal (MinGoal dgoal) = null dgoal
  mapGoal (MinGoal dgoal) f = MinGoal (f dgoal)
  unfoldStep = genUnfoldStep splitGoal MinGoal

--splitGoal :: E.Env -> MinGoal -> (G S, DGoal)
--splitGoal env (MinGoal gs) = let (c:cs) = sortBy (compareGoals env) gs
--                    in (c, cs)

splitGoal :: E.Env -> MinGoal -> (DGoal, G S, DGoal)
splitGoal env (MinGoal gs) =
  let c = minimumBy (compareGoals env) gs
  in fromJust $ split (c ==) gs

compareGoals :: E.Env -> G a -> G a -> Ordering
compareGoals env (Invoke g1 _) (Invoke g2 _)
  | g1 == g2
  = EQ
  | otherwise
  = let n1 = length $ normalize $ trd3 $ E.envLookupDef env g1
        n2 = length $ normalize $ trd3 $ E.envLookupDef env g2
    in compare n1 n2
compareGoals _ _ _ = EQ
