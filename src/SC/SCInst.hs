module SC.SCInst where

import Data.Maybe (fromJust)

import Syntax

import SC.DTree
import SC.SC
import SC.SC1
import SC.SC2

import qualified SC.Unfold.SeqUnfold as SU
import qualified SC.Unfold.FullUnfold as FU
import qualified SC.Unfold.RandUnfold as RU
import qualified SC.Unfold.NonRecUnfold as NU
import qualified SC.Unfold.RecUnfold as RecU
import qualified SC.Unfold.MaxUnfold as MaxU
import qualified SC.Unfold.MinUnfold as MinU
import qualified SC.Unfold.FirstUnfold as FstU

scConfs1 :: [(String, SuperComp)]
scConfs1 =
  [ ("SU",  supercomp (derive1 :: Derive SU.SUGoal))
  , ("FU",  supercomp (derive1 :: Derive FU.FUGoal))
  , ("NU",  supercomp (derive1 :: Derive NU.NUGoal))
  , ("RU",  supercomp (derive1 :: Derive RecU.RecGoal))
  , ("MxU", supercomp (derive1 :: Derive MaxU.MaxGoal))
  , ("MnU", supercomp (derive1 :: Derive MinU.MinGoal))
  , ("FstU", supercomp (derive1 :: Derive FstU.FstGoal))
  ]

scConfs2 :: [(String, SuperComp)]
scConfs2 =
  [ ("SU",  supercomp (derive2 :: Derive SU.SUGoal))
  , ("FU",  supercomp (derive2 :: Derive FU.FUGoal))
  , ("NU",  supercomp (derive2 :: Derive NU.NUGoal))
  , ("RU",  supercomp (derive2 :: Derive RecU.RecGoal))
  , ("MxU", supercomp (derive2 :: Derive MaxU.MaxGoal))
  , ("MnU", supercomp (derive2 :: Derive MinU.MinGoal))
  , ("FstU", supercomp (derive2 :: Derive FstU.FstGoal))
  ]

run1 :: String -> SuperComp
run1 name = fromJust $ lookup name scConfs1

run2 :: String -> SuperComp
run2 name = fromJust $ lookup name scConfs2
