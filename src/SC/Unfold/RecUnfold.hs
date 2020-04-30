module SC.Unfold.RecUnfold where
    
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

newtype RecGoal = RecGoal DGoal deriving Show

instance UnfoldableGoal RecGoal where
  getGoal (RecGoal dgoal)   = dgoal
  initGoal                  = RecGoal     
  emptyGoal (RecGoal dgoal) = null dgoal
  mapGoal (RecGoal dgoal) f = RecGoal (f dgoal)
  unfoldStep = genUnfoldStep splitGoal RecGoal

splitGoal :: E.Env -> RecGoal -> ([G S], G S, [G S])
splitGoal env (RecGoal gs) =
  let c = minimumBy ((compare `on` (not . isRec env)) <> compareGoals env) gs
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
