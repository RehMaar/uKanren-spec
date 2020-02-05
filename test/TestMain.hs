module TestMain where

import System.Process (system)
import System.Exit (ExitCode)
import Data.Maybe
import Text.Printf

import Syntax
import DotPrinter
import SldTreePrinter
import GlobalTreePrinter
import Utils

import qualified CPD
import qualified CpdResidualization as CR
import qualified GlobalControl as GC
import qualified Purification as P
import qualified OCanrenize as OC

import qualified Unfold.SeqUnfold as SU
import qualified Unfold.FullUnfold as FU
import qualified Unfold.RandUnfold as RU
import qualified Unfold.RecUnfold as RecU
import qualified Unfold.UnrecUnfold as UU
import qualified Unfold.Unfold as U

import qualified DTree as DT
import qualified DTResidualize as DTR

import qualified LogicInt as LI
import qualified List as L

import TestUtils


testGoals = []


main :: IO ()
main = undefined

