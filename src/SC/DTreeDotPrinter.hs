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
  labelNode t@(Or ch _ _ _) = addChildren t ch
  labelNode t@(And ch _ _ _) = addChildren t ch
  labelNode t@(Gen ch _) = addChild t ch
  labelNode t = addLeaf t

dotSigma _ = ""
--dotSigma = E.dotSigma

instance Dot DTree where
  dot Fail = "Fail"
  dot (Success s)     = "Success <BR/> " ++ dotSigma s
  dot (Gen _ s)       = printf "Gen <BR/> Generalizer: %s" (E.dotSigma s)
  -- dot (And _ s d _)     = printf "And <BR/> Subst: %s <BR/> Goal: %s" (dotSigma s) (dot d)
  dot (And _ s d a)     = printf "And <BR/> Subst: %s <BR/> Goal: %s <BR/> Anc: %s" (dotSigma s) (dot d) (show $ dot <$> findAnc d a)
  dot (Or ts s d _)     = printf "Or <BR/> Subst: %s <BR/> Goal: %s" (dotSigma s) (dot d)
  dot (Leaf goal ancs s _) = printf "Leaf <BR/> Subst: %s <BR/> Goal: %s <BR/> Anc: %s" (dot goal)  (dotSigma s) (show $ dot <$> findRenaming goal ancs)
  dot (Prune g)       = printf "Prune <BR/> Goal: %s" (dot g)
