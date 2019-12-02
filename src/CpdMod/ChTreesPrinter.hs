module CpdMod.ChTreesPrinter where

import DotPrinter
import Syntax (Dot(..))
import CPD
import Eval as E
import CpdMod.GlobalControlCA
import CpdMod.ChAtoms
import Text.Printf

instance DotPrinter ChTree where
  labelNode t@(ChRoot ch) = addChildren t ch
  labelNode t@(ChBranch _ ch) = addChildren t ch
  labelNode t = addLeaf t

instance Dot ChTree where
  dot (ChRoot _) = "Root"
  dot (ChNode ca) = show ca
  dot (ChBranch ca _) = show ca


instance Dot a => DotPrinter (ChAtom a) where
  labelNode = labelNode . chTree

instance Dot a => Dot (ChAtom a) where
  dot (ChAtom atom tree) = dot atom ++ " " ++ dot tree

instance DotPrinter SldTreeInner where
  labelNode t@(CConj ch _ _ _) = addChild    t ch
  labelNode t@(OOr ch _)     = addChildren t (snd <$> ch)
  labelNode t                = addLeaf     t

instance Dot SldTreeInner where
  dot (LLeaf gs s _) = printf "Leaf <BR/> %s <BR/> %s" (dot (map getCurr gs)) (E.dotSigma s)
  dot FFail = "_|_"
  dot (SSuccess s i) = printf "S (%d) <BR/> %s" i (E.dotSigma s)
  dot (OOr ch _ ) = printf $ "O: " ++ show (fst <$> ch) -- <BR/> " ++ dot curr
  dot (CConj _ gs s i)  = printf "C (%d) <BR/> %s <BR/> %s" i (dot $ map getCurr gs) (E.dotSigma s) -- %s <BR/> %s" (show id') (dot curr)

instance DotPrinter GlobalTreeCh where
  labelNode t@(NodeCh _ _ _ ch) i vs es ids = addChildren t ch i vs es ids
  labelNode t                   i vs es ids = addLeaf     t    i vs es ids

instance Dot GlobalTreeCh where
  dot (LeafCh gs _ s)  = printf "L <BR/> %s <BR/> %s" ({-show s-} "") (dot $ getCurr gs)
  dot (NodeCh (Descend atom _) gen _ _) = printf "N <BR/> %s <BR/> %s <BR/> %s" (dot (chAtom atom)) ({-show gen-} "") (show (chTree atom))
  dot (PruneCh gs _  _)  = printf "P <BR/> %s" (dot $ getCurr gs)
