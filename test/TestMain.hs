module TestMain where

import System.Process (system)
import System.Exit (ExitCode)
import Data.Maybe
import Text.Printf

import Syntax
import DotPrinter
import CPD.SldTreePrinter
import CPD.GlobalTreePrinter
import Utils

import qualified CPD.LocalControl as CPD
import qualified CPD.CpdResidualization as CR
import qualified CPD.GlobalControl as GC
import qualified Purification as P
import qualified OCanrenize as OC

import qualified SC.Unfold.SeqUnfold as SU
import qualified SC.Unfold.FullUnfold as FU
import qualified SC.Unfold.RandUnfold as RU
import qualified SC.Unfold.RecUnfold as RecU
import qualified SC.Unfold.NonRecUnfold as NU
import qualified SC.SC as U

import qualified SC.DTree as DT
import qualified SC.DTResidualize as DTR

import qualified LogicInt as LI
import qualified List as L

import TestUtils


testGoals = []


main :: IO ()
main = undefined

