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


scomp1SU  = supercomp (derive1 :: Derive SU.SUGoal)
scomp1FU  = supercomp (derive1 :: Derive FU.FUGoal)
scomp1NU  = supercomp (derive1 :: Derive NU.NUGoal)
scomp1RcU = supercomp (derive1 :: Derive RecU.RecGoal)
scomp1MxU = supercomp (derive1 :: Derive MaxU.MaxGoal)
scomp1MnU = supercomp (derive1 :: Derive MinU.MinGoal)
scomp1FsU = supercomp (derive1 :: Derive FstU.FstGoal)

scConfs1 :: [(String, SuperComp)]
scConfs1 =
  [ ("SU",   scomp1SU )
  , ("FU",   scomp1FU )
  , ("NU",   scomp1NU )
  , ("RU",   scomp1RcU)
  , ("MxU",  scomp1MxU)
  , ("MnU",  scomp1MnU)
  , ("FstU", scomp1FsU)
  ]


scomp2SU  = supercomp (derive2 :: Derive SU.SUGoal)
scomp2FU  = supercomp (derive2 :: Derive FU.FUGoal)
scomp2NU  = supercomp (derive2 :: Derive NU.NUGoal)
scomp2RcU = supercomp (derive2 :: Derive RecU.RecGoal)
scomp2MxU = supercomp (derive2 :: Derive MaxU.MaxGoal)
scomp2MnU = supercomp (derive2 :: Derive MinU.MinGoal)
scomp2FsU = supercomp (derive2 :: Derive FstU.FstGoal)

scConfs2 :: [(String, SuperComp)]
scConfs2 =
  [ ("SU",   scomp2SU )
  , ("FU",   scomp2FU )
  , ("NU",   scomp2NU )
  , ("RU",   scomp2RcU)
  , ("MxU",  scomp2MxU)
  , ("MnU",  scomp2MnU)
  , ("FstU", scomp2FsU)
  ]

run1 :: String -> SuperComp
run1 name = fromJust $ lookup name scConfs1

run2 :: String -> SuperComp
run2 name = fromJust $ lookup name scConfs2
