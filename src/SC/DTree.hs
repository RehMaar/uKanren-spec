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
data DTree' a = Fail   -- Failed derivation.
  | Success E.Sigma -- Success derivation.
  | Or [DTree' a] E.Sigma a (Set.Set DGoal) -- Node for a disjunction.
  | And [DTree' a] E.Sigma a  (Set.Set DGoal)  -- Node for a conjunction.
  | Leaf a (Set.Set DGoal) E.Sigma E.Gamma -- Variant leaf
  | Gen (DTree' a) E.Sigma -- Generalizer
  | Prune a -- Debug node
  | Debug E.Gamma E.Sigma DGoal (Set.Set DGoal) -- Debug node

type DTree = DTree' DGoal

--

instance Show a => Show (DTree' a) where
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
countLeafs Leaf{} = (1, 0, 0)
countLeafs (Success _) = (0, 1, 0)
countLeafs Fail = (0, 0, 1)
countLeafs _ = (0, 0, 0)

countDepth :: DTree -> Int
countDepth (Or ts _ _ _) = 1 + foldl max 0 (countDepth <$> ts)
countDepth (And ts _ _ _) = 1 + foldl max 0 (countDepth <$> ts)
countDepth (Gen t _) = countDepth t
countDepth _ = 1

countNodes :: DTree -> Int
countNodes (Or ts _ _ _) = 1 + sum (countNodes <$> ts)
countNodes (And ts _ _ _) = 1 + sum (countNodes <$> ts)
countNodes (Gen t _) = 1 + countNodes t
countNodes _ = 1

countPrunes :: DTree -> Int
countPrunes (Or ts _ _ _) = sum (countPrunes <$> ts)
countPrunes (And ts _ _ _) = sum (countPrunes <$> ts)
countPrunes (Gen t _) = countPrunes t
countPrunes (Prune _) = 1
countPrunes _ = 0

-- Utils

findFirst f = getFirst . foldMap (First . f)
