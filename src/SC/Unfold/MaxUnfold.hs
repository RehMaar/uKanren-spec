module SC.Unfold.MaxUnfold where
    
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

newtype MaxGoal = MaxGoal DGoal deriving Show

instance UnfoldableGoal MaxGoal where
  getGoal (MaxGoal dgoal) = dgoal
  initGoal      = MaxGoal
  emptyGoal (MaxGoal dgoal) = null dgoal
  mapGoal (MaxGoal dgoal) f = MaxGoal (f dgoal)
  unfoldStep = genUnfoldStep splitGoal MaxGoal

splitGoal :: E.Env -> MaxGoal -> (DGoal, G S, DGoal)
splitGoal env (MaxGoal gs) =
  let c = minimumBy (compareGoals env) gs
  in fromJust $ split (c ==) gs

compareGoals :: E.Env -> G a -> G a -> Ordering
compareGoals env (Invoke g1 _) (Invoke g2 _)
  | g1 == g2
  = EQ
  | otherwise
  = let n1 = length $ normalize $ trd3 $ E.envLookupDef env g1
        n2 = length $ normalize $ trd3 $ E.envLookupDef env g2
    in compare n2 n1
compareGoals _ _ _ = EQ
