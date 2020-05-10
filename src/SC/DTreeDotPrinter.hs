module SC.DTreeDotPrinter where

import qualified Eval as E
import Syntax
import DotPrinter
import SC.DTree
import Text.Printf
import SC.SC
import Data.Maybe (fromJust)

--
instance DotPrinter DTree where
  labelNode t@(Unfold ch _ _ _) = addChildren t ch
  labelNode t@(Abs ch _ _ _) = addChildren t ch
  labelNode t@(Gen ch _) = addChild t ch
  labelNode t = addLeaf t

--dotSigma _ = ""
dotSigma = E.dotSigma

instance Dot DTree where
  dot Fail = "Fail"
  dot (Success s c)       = "Success <BR/> " ++ dotSigma s ++ "<BR/>CS: " ++ dotSigma c
  dot (Gen _ s)         = printf "Gen <BR/> Generalizer: %s" (E.dotSigma s)
  dot (Abs _ s c d)       = printf "Abs <BR/> Subst: %s <BR/> CS: %s <BR/> Goal: %s" (dotSigma s) (dotSigma c) (dot d)
  dot (Unfold ts s c d)   = printf "Unfold <BR/> Subst: %s <BR/> CS: %s <BR/> Goal: %s" (dotSigma s) (dotSigma c) (dot d)
  dot (Renaming goal s c) = printf "Renaming <BR/> Subst: %s <BR/> CS: %s <BR/> Goal: %s" (dotSigma s) (dotSigma c) (dot goal)
  dot (Prune g)         = printf "Prune <BR/> Goal: %s" (dot g)
