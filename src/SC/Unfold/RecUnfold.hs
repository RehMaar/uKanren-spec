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

data RecGoal = RecGoal DGoal Int deriving Show

instance UnfoldableGoal RecGoal where
  getGoal (RecGoal dgoal _)   = dgoal
  initGoal goal              = RecGoal goal 0
  emptyGoal (RecGoal dgoal _) = null dgoal
  mapGoal (RecGoal dgoal i) f = RecGoal (f dgoal) i
  -- unfoldStep = genUnfoldStep splitGoal RecGoal
  unfoldStep = recUnfoldStep

splitGoal :: E.Env -> RecGoal -> ([G S], G S, [G S])
splitGoal env (RecGoal gs _) =
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

recUnfoldStep (RecGoal dgoal idx) env subst cstore = let
    (idx', (ls, conjs, rs)) = splitGoal'' env idx dgoal
    (newEnv, uConj) = unfoldAll env conjs
    nConj = conjOfDNFtoDNF (goalToDNF <$> uConj)
    unConj = unifyAll subst cstore nConj
    us = (\(cs, subst, cstore) -> (subst, cstore, suGoal idx' subst cs ls rs)) <$> unConj
  in (us, newEnv)
  where
    suGoal idx' subst cs ls rs = RecGoal (E.substitute subst $ ls ++ cs ++ rs) idx'

splitGoal'' env idx gs =
  case partition (isRec env) gs of
     (ls, []) -> splitSeq idx ls -- let (l, c, r) = getWithMinBody ls in (l, [c], r)
     (ls, rs) -> (0, ([], rs, ls))
  where
    getWithMinBody gs =
      let c = minimumBy ((compare `on` (not . isRec env)) <> compareGoals env) gs
      in fromJust $ split (c ==) gs

splitSeq _ [g] = (0, ([], [g], []))
splitSeq idx gs = let
  (ls, rs) = splitAt idx gs
  in case uncons rs of
      Just (c, []) -> (idx, (ls, [c], []))
      Just (c, rs) -> (succ idx, (ls, [c], rs))
      Nothing -> case uncons gs of
                    Just (g, gs') -> (1, ([], [g], gs'))
                    _ -> error "Split unsplitable"
