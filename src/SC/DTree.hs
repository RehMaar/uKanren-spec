module SC.DTree where

import Syntax
import Embedding

import qualified CPD.LocalControl as CPD
import qualified CPD.GlobalControl as GC
import qualified Eval as E

import qualified Data.Set as Set
import Data.Monoid

import Data.Maybe (mapMaybe, isJust, fromJust)
import Text.Printf
import DotPrinter

import Debug.Trace

type Conj a = [a]
type Disj a = [a]

type DGoal = Conj (G S)

-- Conjunction of invokes and substitutions
type DDescendGoal = CPD.Descend DGoal

-- Simple initial constractor.
dGoal :: G S -> Set.Set [G S] -> DDescendGoal
dGoal goal ancs = CPD.Descend [goal] ancs

-- Logic expression to DNF
goalToDNF :: G S -> Disj (Conj (G S))
goalToDNF = CPD.normalize

-- Derivation Tree
data DTree = Fail   -- Failed derivation.
  | Success E.Sigma -- Success derivation.
  | Or [DTree] E.Sigma DDescendGoal -- Node for a disjunction.
  | And [DTree] E.Sigma DDescendGoal -- Node for a conjunction.
  | Leaf DDescendGoal E.Sigma E.Gamma -- Variant leaf
  | Gen DTree E.Sigma -- Generalizer
  -- Not in use now
  | Node DTree DDescendGoal E.Sigma -- Auxiliary node.
  | Prune DGoal -- Debug node
  | Debug E.Gamma E.Sigma DGoal (Set.Set DGoal) -- Debug node


--
instance DotPrinter DTree where
  labelNode t@(Or ch _ _) = addChildren t ch
  labelNode t@(And ch _ _) = addChildren t ch
  labelNode t@(Node ch _ _) = addChild t ch
  labelNode t@(Gen ch _) = addChild t ch
  labelNode t = addLeaf t

dotSigma _ = ""
-- dotSigma = E.dotSigma

instance Dot DTree where
  dot Fail = "Fail"
  dot (Success s)     = "Success <BR/> " ++ (dotSigma s)
  dot (Node _ d s)    = printf "Node <BR/> Goal: %s <BR/> Subst: %s" (dot $ CPD.getCurr d)  (dotSigma s)
  dot (Gen _ s)       = printf "Gen <BR/> Generalizer: %s" (dotSigma s)
  dot (And _ s d)     = printf "And <BR/> Subst: %s <BR/> Goal: %s" (dotSigma s) (dot $ CPD.getCurr d)
  dot (Or ts s d)     = printf "Or <BR/> Subst: %s <BR/> Goal: %s" (dotSigma s) (dot $ CPD.getCurr d)
  dot (Leaf goal s _) = printf "Leaf <BR/> Goal: %s <BR/> Subst: %s" (dot $ CPD.getCurr goal)  (dotSigma s)
  dot (Prune g)       = printf "Prune <BR/> Goal: %s" (dot g)

--

instance Show DTree where
  show Fail = "Fail"
  show (Success s) = "{Success}"
  show (Or ts _ goal) = "{Or \n [" ++ concatMap show ts ++ "]\n}"
  show (And ts _ goal) = "{And \n [" ++ concatMap show ts ++ "]\n}"
  show (Node t d s) = "{Node [" ++ show t ++ "]\n}"
  show (Gen t s) = "{Gen  " ++ show t ++ "\n}"
  show (Leaf g _ _) = "{Leaf " ++ show g ++ "}"
  show (Prune d) = "{Prune " ++ show d ++ "}"
  show (Debug env subst goal ancs) = "{Debug " ++ show goal ++ "}"

--
-- Return list of goals of tree's leaves (`Leaf` nodes)
--
leaves :: DTree -> [DGoal]
leaves (Or ts _ _) = concatMap leaves ts
leaves (And ts _ _) = concatMap leaves ts
leaves (Leaf g _ _) = [CPD.getCurr g]
leaves (Gen t _) = leaves t
leaves _ = []

---

findVariantNode :: DGoal ->  DTree -> Maybe DTree
findVariantNode dg n@(Or ts _ g)
  | isVariant (CPD.getCurr g) dg
  = Just n
  | otherwise
  = findFirst (findVariantNode dg) ts
findVariantNode dg n@(And ts _ g)
  | isVariant (CPD.getCurr g) dg
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
treeGoals (Or ts _ goal)  = Set.insert (CPD.getCurr goal) (Set.unions (treeGoals <$> ts))
treeGoals (And ts _ goal) = Set.insert (CPD.getCurr goal) (Set.unions (treeGoals <$> ts))
-- treeGoals (Node t goal _) = Set.insert (CPD.getCurr goal) (treeGoals t)
-- treeGoals (Leaf goal _ _) = Set.singleton (CPD.getCurr goal)
treeGoals (Gen t _) = treeGoals t
-- treeGoals (Prune goal) = Set.singleton (CPD.getCurr goal)
treeGoals _ = Set.empty

--
-- Evaluate tree's metrics.
--

--                    (leafs, Success, Fail)
countLeafs :: DTree -> (Int, Int, Int)
countLeafs (Or ts _ _) = foldl (\(n1, m1, h1) (n2, m2, h2) -> (n1 + n2, m1 + m2, h1 + h2)) (0, 0, 0) (countLeafs <$> ts)
countLeafs (And ts _ _) = foldl (\(n1, m1, h1) (n2, m2, h2) -> (n1 + n2, m1 + m2, h1 + h2)) (0, 0, 0) (countLeafs <$> ts)
countLeafs (Node t _ _) = countLeafs t
countLeafs (Gen t _) = countLeafs t
countLeafs (Leaf _ _ _) = (1, 0, 0)
countLeafs (Success _) = (0, 1, 0)
countLeafs Fail = (0, 0, 1)
countLeafs _ = (0, 0, 0)

countDepth :: DTree -> Int
countDepth (Or ts _ _) = 1 + foldl max 0 (countDepth <$> ts)
countDepth (And ts _ _) = 1 + foldl max 0 (countDepth <$> ts)
countDepth (Node t _ _) = 1 + countDepth t
countDepth (Gen t _) = 1 + countDepth t
countDepth _ = 1

countNodes :: DTree -> Int
countNodes (Or ts _ _) = 1 + sum (countNodes <$> ts)
countNodes (And ts _ _) = 1 + sum (countNodes <$> ts)
countNodes (Node t _ _) = 1 + countNodes t
countNodes (Gen t _) = 1 + countNodes t
countNodes _ = 1

-- Utils

findFirst f = getFirst . foldMap (First . f)
