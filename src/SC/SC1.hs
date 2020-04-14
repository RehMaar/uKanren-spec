{-# LANGUAGE ScopedTypeVariables #-}


module SC.SC1(derive1) where
    
import SC.DTree
import Syntax
import Embedding

import qualified Eval as E
import qualified Purification as P
import qualified Generalization as D

import Utils
import DotPrinter

import Data.Maybe (mapMaybe)
import Data.List (group, sort, groupBy, find, intersect, delete, sortBy)
import qualified Data.Set as Set
import Data.Tuple (swap)

import Text.Printf
import Debug.Trace

import Control.Arrow (first)
import Control.Exception
import PrettyPrint

import SC.SC

{-
Supercompiler's properties:
* Forbid generalization after generalization.
* Allow generalization on ancestors.
-}
derive1 :: UnfoldableGoal a => Derive a
derive1 = Derive derive'

derive' :: UnfoldableGoal a =>
     a                 -- |Conjunction of invokes and substs.
  -> [DGoal]           -- |Ancsectors.
  -> E.Env             -- |Context.
  -> E.Subst           -- |Substitution.
  -> Set.Set DGoal     -- |Already seen.
  -> Int -- depth for debug
  -> (DTree, Set.Set DGoal, S)
derive' goal ancs env subst seen depth
    | checkLeaf (getGoal goal) seen
    = (Renaming (getGoal goal) subst, seen, maxFreshVar env)
    | otherwise
    = 
    let
      realGoal = getGoal goal
      newAncs = realGoal : ancs
    in case unfoldStep goal env subst of
       ([], _)          -> (Fail, seen, maxFreshVar env)
       (uGoals, newEnv) ->
         let
           newSeen = Set.insert realGoal seen
           (seen', ts, maxVarNum) = foldl (\(seen, ts, m) g ->
               (\(a, t, i) -> (a, t:ts, max i m)) $
                 evalSubTree' (succ depth) (fixEnv m newEnv) newAncs seen g)
               (newSeen, [], maxFreshVar env) uGoals
         in (Unfold (reverse ts) subst realGoal, seen', maxVarNum)
   where
    evalSubTree' :: UnfoldableGoal a => Int -> E.Env -> [DGoal] -> Set.Set DGoal -> (E.Subst, a) -> (Set.Set DGoal, DTree, S)
    evalSubTree' depth env ancs seen (subst, goal :: a)
     | emptyGoal goal
     = {-trace ">Success" $-} (seen, Success subst, maxFreshVar env)
     | not (checkLeaf realGoal seen)
     , isGen realGoal (Set.fromList ancs)
     =
      -- trace (">Abstract: " ++ pretty realGoal {-++ "; anc: " ++ show (findAnc realGoal ancs)-}) $
      let
        (absGoals, ns') = abstractL ancs realGoal (E.envNS env)
        -- Add `realGoal` to a seen set (`Abs` node in the tree).
        newSeen = Set.insert realGoal seen
        newEnv  = env{E.envNS = ns'}
      in {-trace (">>Got " ++ show (length absGoals) ++ " subgoals") $-} let
        (seen', ts, maxVarNum) = foldl (\(seen, ts, m) g ->
                (\(a, t, i) -> (a, t:ts, max i m)) $
                 evalGenSubTree m (succ depth) ancs seen newEnv subst g)
                 (newSeen, [], maxFreshVar env) absGoals
          in (seen', Abs (reverse ts) subst realGoal, maxVarNum)
        | otherwise
        =
          let
            (tree, seen', maxVarNum) = derive' goal ancs env subst seen depth
          in (seen', tree, maxVarNum)
        where
          realGoal = getGoal goal

          evalGenSubTree m depth ancs seen env subst (goal, gen) =
            let
              env' = fixEnv m env
              igoal :: a = initGoal goal
              (tree, seen', maxVarNum) = derive' igoal ancs env' subst seen depth
              subtree  = if null gen then tree else Gen tree gen
            in (seen', subtree, maxVarNum)
