module SC.SC3 (derive3) where

import SC.DTree
import Syntax
import Embedding

import qualified Eval as E
-- import qualified Driving as D
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
* Allow generalization after generalization.
* Allow generalization on ancestors.
-}
derive3 :: UnfoldableGoal a => Derive a
derive3 = Derive derive'

derive' :: UnfoldableGoal a => Derivable a
derive' = derivationStep'
    where
      abstractSame [(_, aGoal, _, _)] goal = isVariant aGoal goal
      abstractSame _ _ = False

      derivationStep' goal ancs env subst seen d
        -- Empty goal => everything evaluated fine
        | emptyGoal goal
        = (Success subst, seen, maxFreshVar env)
        -- If we already seen the same node, stop evaluate it.
        | checkLeaf (getGoal goal) seen
        = (Renaming (getGoal goal) ancs subst env, seen, maxFreshVar env)
        -- If a node is generalization of one of ancsectors generalize.
        | isGen (getGoal goal) ancs
        , aGoals <- abstract ancs (getGoal goal) subst env
        , not $ abstractSame aGoals (getGoal goal)
        =
          -- trace ("\nAbstract: " ++ show (getGoal goal)) $
          let
            rGoal = getGoal goal
            --aGoals = abstract ancs rGoal subst env
          -- in trace ("Goal: " ++ pretty rGoal
          --         ++ "\nAbs:  " ++ show ((\(_,g,_,_) -> pretty g) <$> aGoals) ++ "\n"
          --         ++ "Ancs: " ++ show ancs ++ "\n"
          --         ) $
          -- let
            nAncs = Set.insert rGoal ancs
            nSeen = Set.insert rGoal seen
            (seen', trees, maxVarNum) =
              foldl
                (\(seen, ts, m) (subst, goal, gen, nEnv) ->
                  let (t, seen'', mv) = derivationStep' (initGoal goal) nAncs (fixEnv m nEnv) subst seen (succ d)
                      t' = if null gen then t else Gen t gen
                  in (seen'', t':ts, mv)
                )
                (nSeen, [], maxFreshVar env)
                aGoals
            tree = Abs (reverse trees) subst rGoal ancs
          in (tree, seen', maxVarNum)
        | otherwise
        = case unfoldStep goal env subst of
            ([], _) -> (Fail, seen, maxFreshVar env)
            (uGoals, nEnv) -> let
                rGoal = getGoal goal
                nAncs = Set.insert rGoal ancs
                nSeen = Set.insert rGoal seen

                (seen', trees, maxVarNum) =
                  foldl
                    (\(seen, ts, m) (subst, goal) ->
                      let (t, seen'', mv) = derivationStep' goal nAncs (fixEnv m nEnv) subst seen (succ d)
                      in (seen'', t:ts, mv)
                    )
                    (nSeen, [], maxFreshVar nEnv)
                    uGoals
                tree = Unfold (reverse trees) subst rGoal ancs
              in (tree, seen', maxVarNum)
