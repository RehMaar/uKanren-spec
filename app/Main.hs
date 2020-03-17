module Main where

import Syntax
import qualified SC.DTree as DT
import qualified SC.SCInst as SCI
import qualified SC.SC as SC
import qualified SC.DTResidualize as DTR
import qualified Purification as P
import qualified OCanrenize as OC

import TestUtils as TU
import DotPrinter
import Utils

import System.Exit (ExitCode)

-- Programs
import qualified LogicInt as LI
import qualified Path
import qualified Unify
import qualified Programs as P
import qualified Bool as B

-- | Full Unfold
--   Working version
--   Not working: SCI.scomp1FU
specializer = SCI.scomp2FU

-- Run a supercompiler to get a residual program.
runSC
  :: SC.SuperComp  -- | Supercompiler to run.
  -> String        -- | Name of toplevel method.
  -> FilePath      -- | Path to save a resulting program.
  -> G X           -- | Goal to specialize>
  -> IO ()
runSC = TU.ocanrenGen

-- Print a tree
printToPdf
  :: DotPrinter a
  => String      -- | Filename
  -> a           -- | An entity to print
  -> IO ExitCode
printToPdf = TU.printToPdf

-- Logic interpreter query
logintQuery = LI.loginto $ fresh ["subst", "formula"] $ call "loginto" [V "subst", V "formula", B.trueo]

logintTree = fst3 $ specializer logintQuery

main :: IO ()
main = runSC specializer "logintTopLevel" "loginto.ml" logintQuery
