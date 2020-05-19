module SC.Unfold.NonRecUnfold where
    
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

data NUGoal = NUGoal DGoal Int deriving Show

instance UnfoldableGoal NUGoal where
  getGoal (NUGoal dgoal _) = dgoal
  initGoal = flip NUGoal 0
  emptyGoal (NUGoal dgoal _) = null dgoal
  mapGoal (NUGoal dgoal idx) f = NUGoal (f dgoal) idx
  unfoldStep = unreqUnfoldStep'''

unreqUnfoldStep (NUGoal dgoal idx) env subst cstore = let
    (ls, conj, rs) = splitGoal env dgoal
    (newEnv, uConj) = unfold conj env

    nConj = goalToDNF uConj
    unConj = unifyAll subst cstore nConj
    us = (\(cs, subst, cstore) -> (subst, cstore, suGoal subst cs ls rs)) <$> unConj
  in (us, newEnv)
  where
    suGoal subst cs ls rs = NUGoal (E.substitute subst $ ls ++ cs ++ rs) idx

splitGoal :: E.Env -> DGoal -> ([G S], G S, [G S])
splitGoal env gs =
   let c = minimumBy ((compare `on` isRec env) <> compareGoals env) gs
   in fromJust $ split (c ==) gs

-- Return value is Conj (G S), but now (G S) is a body of corresponding Invoke.


unreqUnfoldStep' (NUGoal dgoal idx) env subst cstore = let
    (ls, conjs, rs) = splitGoal' env dgoal
    (newEnv, uConj) = unfoldAll env conjs
    nConj = conjOfDNFtoDNF (goalToDNF <$> uConj)
    unConj = unifyAll subst cstore nConj
    us = (\(cs, subst, cstore) -> (subst, cstore, suGoal subst cs ls rs)) <$> unConj
  in (us, newEnv)
  where
    suGoal subst cs ls rs = NUGoal (E.substitute subst $ ls ++ cs ++ rs) idx

splitGoal' :: E.Env -> DGoal -> ([G S], [G S], [G S])
splitGoal' env gs =
  case partition (isRec env) gs of
     (ls, []) -> let (l, c, r) = getWithMinBody ls in (l, [c], r)
     (ls, rs) -> ([], rs, ls)
  where
    getWithMinBody gs =
      let c = minimumBy ((compare `on` isRec env) <> compareGoals env) gs
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


unreqUnfoldStep'' (NUGoal dgoal idx) env subst cstore = let
    (idx', (ls, conjs, rs)) = splitGoal'' env idx dgoal
    (newEnv, uConj) = unfoldAll env conjs
    nConj = conjOfDNFtoDNF (goalToDNF <$> uConj)
    unConj = unifyAll subst cstore nConj
    us = (\(cs, subst, cstore) -> (subst, cstore, suGoal idx' subst cs ls rs)) <$> unConj
  in (us, newEnv)
  where
    suGoal idx' subst cs ls rs = NUGoal (E.substitute subst $ ls ++ cs ++ rs) idx'

splitGoal'' env idx gs =
  case partition (isRec env) gs of
     (ls, []) -> splitSeq idx ls -- let (l, c, r) = getWithMinBody ls in (l, [c], r)
     (ls, rs) -> (0, ([], rs, ls))


unreqUnfoldStep''' (NUGoal dgoal idx) env subst cstore = let
    (idx', (ls, conj, rs)) = splitGoal''' env idx dgoal
    (newEnv, uConj) = unfold conj env

    nConj = goalToDNF uConj
    unConj = unifyAll subst cstore nConj
    us = (\(cs, subst, cstore) -> (subst, cstore, suGoal idx' subst cs ls rs)) <$> unConj
  in (us, newEnv)
  where
    suGoal idx subst cs ls rs = NUGoal (E.substitute subst $ ls ++ cs ++ rs) idx

splitGoal''' env idx gs =
  case partition (isRec env) gs of
     (ls, []) -> let (i, (a, [g], b)) = splitSeq idx ls in (i, (a, g, b))
     (ls, r:rs) -> (0, (ls, r, rs))

-- splitGoal'' :: E.Env -> DGoal -> ([G S], [G S], [G S])
splitSeq _ [g] = (0, ([], [g], []))
splitSeq idx gs = let
  (ls, rs) = splitAt idx gs
  in case uncons rs of
      Just (c, []) -> (idx, (ls, [c], []))
      Just (c, rs) -> (succ idx, (ls, [c], rs))
      Nothing -> case uncons gs of
                    Just (g, gs') -> (1, ([], [g], gs'))
                    _ -> error "Split unsplitable"
