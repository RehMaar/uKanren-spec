module SC.Unfold.RandUnfold where
    
import Syntax
import SC.DTree
import Utils

import qualified Eval as E
import qualified Purification as P
import qualified SC.Unfold.SeqUnfold as SU

import SC.SC

import Data.Maybe (mapMaybe)
import Data.List
import qualified Data.Set as Set
import System.Random
import Control.Monad

import Text.Printf
import DotPrinter

import Debug.Trace

data RndGoal = RndGoal DGoal StdGen deriving Show

firstFreeVar = head . E.envNS

{-topLevel :: Int -> G X -> (DTree, G S, [S])
topLevel seed g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  igoal = RndGoal [lgoal] (mkStdGen seed)
  tree = fst3 $ derivationStep igoal Set.empty lgamma E.s0 Set.empty 0
  in (tree, lgoal, lnames)
  where
    randUnfoldStep :: RndGoal -> E.Env -> E.Subst -> ([(E.Subst, RndGoal)], E.Env)
    randUnfoldStep (RndGoal dgoal rng) env subst = let
        len = length dgoal

        (idx, rng') = randomR (0, len) rng

        (_, (ls, conj, rs)) = SU.splitGoal idx dgoal

        (newEnv, uConj) = unfold conj env
        nConj = goalToDNF uConj
        unConj = unifyAll subst nConj
        us = (\(cs, subst) -> (subst, rndGoal subst ls cs rs rng')) <$> unConj

      in (us, newEnv)
      where
        rndGoal subst ls cs rs rng = let
            goal = ls ++ cs ++ rs
            dgoal = E.substitute subst goal
          in RndGoal dgoal rng

    derivationStep goal@(RndGoal realGoal rng) ancs env subst seen depth
      | checkLeaf realGoal seen
      = (Renaming realGoal ancs subst env, seen, firstFreeVar env)
      | otherwise
      =
      let
        newAncs = Set.insert realGoal ancs
      in case randUnfoldStep goal env subst of
         ([], _)          -> (Fail, seen, firstFreeVar env)
         (uGoals, newEnv) -> let
             newSeen = Set.insert realGoal seen
             (seen', ts, maxVarNum) = foldl (\(seen, ts, m) g ->
                 (\(a, t, i) -> (a, t:ts, max i m)) $
                   evalSubTree depth (fixEnv m newEnv) newAncs seen g)
                 (newSeen, [], firstFreeVar env) uGoals
           in (Unfold (reverse ts) subst realGoal ancs, seen', maxVarNum)

    evalSubTree depth env ancs seen (subst, goal@(RndGoal realGoal rng))
      | null realGoal
      = (seen, Success subst, firstFreeVar env)
      | not (checkLeaf realGoal seen)
      , isGen realGoal ancs
      =
        let
          absGoals = abstract ancs realGoal subst env
          newSeen = Set.insert realGoal seen

          (seen', ts, maxVarNum) = foldl (\(seen, ts, m) g ->
                  (\(a, t, i) -> (a, t:ts, max i m)) $
                  evalGenSubTree m depth ancs seen rng g)
                  (newSeen, [], firstFreeVar env) absGoals
        in (seen', Abs (reverse ts) subst realGoal ancs, maxVarNum)
      | otherwise
      =
        let
          newDepth = 1 + depth
          (tree, seen', maxVarNum) = derivationStep goal ancs env subst seen newDepth
        in (seen', tree, maxVarNum)
      where
        evalGenSubTree m depth ancs seen rng (subst, goal, gen, env') =
          let
            env = fixEnv m env'
            newDepth = if null gen then 2 + depth else 3 + depth
            rngGoal = RndGoal goal rng
            (tree, seen', maxVarNum) = derivationStep rngGoal  ancs env subst seen newDepth
            subtree  = if null gen then tree else Gen tree gen
          in (seen', subtree, maxVarNum)-}

--
-- Implementation of the Random Unfolding rule using global randomizer.
--
{-newtype RndGoalIO = RndGoalIO DGoal deriving Show


topLevelIO :: G X -> IO (DTree, G S, [S])
topLevelIO g = do
  let (lgoal, lgamma, lnames) = goalXtoGoalS g
  let igoal = RndGoalIO [lgoal]
  (tree, _) <- derivationStepIO igoal Set.empty lgamma E.s0 Set.empty 0
  pure (tree, lgoal, lnames)
  where
    randUnfoldStepIO :: RndGoalIO -> E.Env -> E.Subst -> IO ([(E.Subst, RndGoalIO)], E.Env)
    randUnfoldStepIO (RndGoalIO dgoal) env subst = do
        let len' = length dgoal
        let len = if len' == 0 then 0 else pred len'
        idx <- randomRIO (0, len)

        let (_, (ls, conj, rs)) = SU.splitGoal idx dgoal

        let (newEnv, uConj) = unfold conj env
        let nConj = goalToDNF uConj
        let unConj = unifyAll subst nConj
        let us = (\(cs, subst) -> (subst, rndGoal subst ls cs rs)) <$> unConj

        pure (us, newEnv)
      where
        rndGoal subst ls cs rs = let
            goal = ls ++ cs ++ rs
            dgoal = E.substitute subst goal
          in RndGoalIO dgoal


    derivationStepIO
      :: RndGoalIO         -- Conjunction of invokes and substs.
      -> Set.Set DGoal     -- Ancsectors.
      -> E.Env           -- Context.
      -> E.Subst           -- Substitution.
      -> Set.Set DGoal     -- Already seen.
      -> Int               -- Depth for debug.
      -> IO (DTree, Set.Set DGoal)
    derivationStepIO rg@(RndGoalIO goal) ancs env subst seen depth
      -- | depth >= 50
      -- = (Prune (getGoal goal), seen)
      | checkLeaf goal seen
      = pure (Renaming goal subst, seen)
      | otherwise
      = do
        let realGoal = goal
        let newAncs = Set.insert realGoal ancs
        -- Add `goal` to a seen set (`Unfold` node in the tree).
        let newSeen = Set.insert realGoal seen
        (l, r) <- randUnfoldStepIO rg env subst
        case (l, r) of
          ([], _)          -> pure (Fail, seen)
          (uGoals, newEnv) -> do
              -- Делаем свёртку, чтобы просмотренные вершины из одного обработанного поддерева
              -- можно было передать в ещё не обработанное.
            (seen', ts) <- foldM (\(seen, ts) g -> fmap (:ts) <$> evalSubTreeIO depth newEnv newAncs seen g) (newSeen, []) uGoals
            pure (Unfold (reverse ts) subst realGoal, seen')


    evalSubTreeIO :: Int -> E.Env -> Set.Set DGoal -> Set.Set DGoal -> (E.Subst, RndGoalIO) -> IO (Set.Set DGoal, DTree)
    evalSubTreeIO depth env ancs seen (subst, rg@(RndGoalIO goal))
      | null goal
      = pure (seen, Success subst)
      | not (checkLeaf realGoal seen)
      , isGen realGoal ancs
      = do
        let absGoals = abstract ancs realGoal subst (E.envNS env)
          -- Add `realGoal` to a seen set (`Abs` node in the tree).
        let newSeen = Set.insert realGoal seen
        (seen', ts) <- foldM (\(seen, ts) g -> fmap (:ts) <$> evalGenSubTree depth ancs seen env g) (newSeen, []) absGoals
        pure (seen', Abs (reverse ts) subst realGoal)
      | otherwise
      = do
        let newDepth = 1 + depth
        (tree, seen') <- derivationStepIO (RndGoalIO goal) ancs env subst seen newDepth
        pure (seen', tree)
      where
        realGoal = goal
        evalGenSubTree depth ancs seen env (subst, goal, gen, ns) = do
          let newDepth = if null gen then 2 + depth else 3 + depth
          (tree, seen') <- derivationStepIO (RndGoalIO goal) ancs (env{E.envNS = ns}) subst seen newDepth
          let subtree  = if null gen then tree else Gen tree gen
          pure (seen', subtree)

-}
