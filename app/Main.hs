module Main where

import Syntax
import qualified SC.DTree as DT
import qualified SC.SCInst as SCI
import qualified SC.SC as SC
import qualified SC.DTResidualize as DTR
import qualified Purification as P
import qualified OCanrenize as OC

import TestUtils as TU

import Utils

-- Programs
import qualified LogicInt as LI
import qualified Path
import qualified Unify
import qualified Programs as P

-- Full Unfold
specializer = SCI.scomp2FU

-- Run a supercompiler to get a residual program.
runSC
  :: SC.SuperComp  -- | Supercompiler to run.
  -> String     -- | Name of toplevel method.
  -> FilePath   -- | Path to save a resulting program.
  -> G X        -- | Goal to specialize>
  -> IO ()
runSC = TU.ocanrenGen

-- Make a list of pruned goals and it's ancestors
prunedAncestors :: DT.DTree -> [(DT.DGoal, [DT.DGoal])]
prunedAncestors = TU.prunesAncs

-- Write a list like above
writeGoalAncs :: String -> [(DT.DGoal, [DT.DGoal])] -> IO ()
writeGoalAncs = TU.writeGoalAncs

-- Examples

-- Double Appendo Query
dappQuery = P.doubleAppendo $ fresh ["a", "b", "c", "d"] $ call "doubleAppendo" [V "a", V "b", V "c", V "d"]

-- Get a tree
dappTree = fst3 $ specializer dappQuery

main :: IO ()
main = runSC specializer "dapp" "dapp.ml" dappQuery
