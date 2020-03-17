module SC.DTree where

import Syntax
import Embedding

import qualified Eval as E

import qualified Data.Set as Set
import Data.Monoid
import Data.Maybe (mapMaybe, isJust, fromJust)
import Data.List (intercalate)
import Text.Printf
import DotPrinter
import PrettyPrint

import Debug.Trace

type Conj a = [a]
type Disj a = [a]

type DGoal = Conj (G S)

instance PrettyPrint DGoal where
    pretty = prettyList

-- Derivation Tree
data DTree = Fail   -- Failed derivation.
  | Success E.Sigma -- Success derivation.
  | Or [DTree] E.Sigma DGoal (Set.Set DGoal) -- Node for a disjunction.
  | And [DTree] E.Sigma DGoal (Set.Set DGoal)  -- Node for a conjunction.
  | Leaf DGoal (Set.Set DGoal) E.Sigma E.Gamma -- Variant leaf
  | Gen DTree E.Sigma -- Generalizer
  -- Not in use now
  | Node DTree DGoal (Set.Set DGoal) E.Sigma -- Auxiliary node.
  | Prune DGoal -- Debug node
  | Debug E.Gamma E.Sigma DGoal (Set.Set DGoal) -- Debug node


{-
--
instance DotPrinter DTree where
  labelNode t@(Or ch _ _ _) = addChildren t ch
  labelNode t@(And ch _ _ _) = addChildren t ch
  labelNode t@(Gen ch _) = addChild t ch
  labelNode t = addLeaf t

dotSigma _ = ""
-- dotSigma = E.dotSigma

instance Dot DTree where
  dot Fail = "Fail"
  dot (Success s)     = "Success <BR/> " ++ (dotSigma s)
  dot (Gen _ s)       = printf "Gen <BR/> Generalizer: %s" (dotSigma s)
  dot (And _ s d _)     = printf "And <BR/> Subst: %s <BR/> Goal: %s" (dotSigma s) (dot d)
  dot (Or ts s d _)     = printf "Or <BR/> Subst: %s <BR/> Goal: %s" (dotSigma s) (dot d)
  dot (Leaf goal _ s _) = printf "Leaf <BR/> Goal: %s <BR/> Subst: %s" (dot goal)  (dotSigma s)
  dot (Prune g)       = printf "Prune <BR/> Goal: %s" (dot g)
-}

--

instance Show DTree where
  show Fail = "Fail"
  show (Success s) = "{Success}"
  show (Or ts _ goal _) = "{Or \n [" ++ concatMap show ts ++ "]\n}"
  show (And ts _ goal _) = "{And \n [" ++ concatMap show ts ++ "]\n}"
  show (Gen t s) = "{Gen  " ++ show t ++ "\n}"
  show (Leaf g _ _ _) = "{Leaf " ++ show g ++ "}"
  show (Prune d) = "{Prune " ++ show d ++ "}"
  show (Debug env subst goal ancs) = "{Debug " ++ show goal ++ "}"

--
-- Return list of goals of tree's leaves (`Leaf` nodes)
--
leaves :: DTree -> [DGoal]
leaves (Or ts _ _ _) = concatMap leaves ts
leaves (And ts _ _ _) = concatMap leaves ts
leaves (Leaf g _ _ _) = [g]
leaves (Gen t _) = leaves t
leaves _ = []

---

findVariantNode :: DGoal ->  DTree -> Maybe DTree
findVariantNode dg n@(Or ts _ g _)
  | isVariant g dg
  = Just n
  | otherwise
  = findFirst (findVariantNode dg) ts
findVariantNode dg n@(And ts _ g _)
  | isVariant g dg
  = Just n
  | otherwise
  = findFirst (findVariantNode dg) ts
findVariantNode dg (Gen t _) = findVariantNode dg t
findVariantNode _ _ = Nothing

--
-- Match leaves' goals and nodes
--
matchVariants :: DTree -> [(DGoal, DTree)]
matchVariants t = fmap fromJust <$>
                  filter (isJust . snd)
                  ((,) <*> flip findVariantNode t <$> leaves t)

--
-- DTree to a set of goals of its nodes
--
treeGoals :: DTree -> Set.Set DGoal
treeGoals (Or ts _ goal _)  = Set.insert goal (Set.unions (treeGoals <$> ts))
treeGoals (And ts _ goal _) = Set.insert goal (Set.unions (treeGoals <$> ts))
treeGoals (Gen t _) = treeGoals t
treeGoals _ = Set.empty

--
-- Evaluate tree's metrics.
--

--                    (leafs, Success, Fail)
countLeafs :: DTree -> (Int, Int, Int)
countLeafs (Or ts _ _ _) = foldl (\(n1, m1, h1) (n2, m2, h2) -> (n1 + n2, m1 + m2, h1 + h2)) (0, 0, 0) (countLeafs <$> ts)
countLeafs (And ts _ _ _) = foldl (\(n1, m1, h1) (n2, m2, h2) -> (n1 + n2, m1 + m2, h1 + h2)) (0, 0, 0) (countLeafs <$> ts)
countLeafs (Gen t _) = countLeafs t
countLeafs (Leaf _ _ _ _) = (1, 0, 0)
countLeafs (Success _) = (0, 1, 0)
countLeafs Fail = (0, 0, 1)
countLeafs _ = (0, 0, 0)

countDepth :: DTree -> Int
countDepth (Or ts _ _ _) = 1 + foldl max 0 (countDepth <$> ts)
countDepth (And ts _ _ _) = 1 + foldl max 0 (countDepth <$> ts)
countDepth (Gen t _) = 1 + countDepth t
countDepth _ = 1

countNodes :: DTree -> Int
countNodes (Or ts _ _ _) = 1 + sum (countNodes <$> ts)
countNodes (And ts _ _ _) = 1 + sum (countNodes <$> ts)
countNodes (Gen t _) = 1 + countNodes t
countNodes _ = 1

-- Utils

findFirst f = getFirst . foldMap (First . f)
