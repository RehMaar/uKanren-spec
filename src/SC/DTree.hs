module SC.DTree where

import           Syntax
import           Embedding

import qualified Eval                          as E

import qualified Data.Set                      as Set
import           Data.Monoid
import           Data.Maybe                               ( mapMaybe
                                                          , isJust
                                                          , fromJust
                                                          )
import           Data.List                                ( intercalate )
import           Text.Printf
import           DotPrinter
import           PrettyPrint

import           Debug.Trace

type Conj a = [a]
type Disj a = [a]

type DGoal = Conj (G S)

instance PrettyPrint DGoal where
  pretty = prettyList

-- |Derivation Tree
data DTree' a =
    Fail
  -- ^Failed derivation.
  | Success E.Sigma
  -- ^Success derivation.
  | Unfold [DTree' a] E.Sigma a (Set.Set DGoal)
  -- ^Intermediate node, that contains a conjunctions.
  -- Its children are parts of a disjunction.
  | Abs [DTree' a] E.Sigma a  (Set.Set DGoal)
  -- ^Node for an abstracted goal.
  | UAbs [DTree' a] E.Sigma a  (Set.Set DGoal) [(S, Ts)]
  -- ^Node for an upward abstracted goal. Also have to save arguments mapping.
  | Renaming a (Set.Set DGoal) E.Sigma E.Gamma
  -- ^An expression in the node is a renaming of any parent (or already seen) node.
  | Gen (DTree' a) E.Sigma
  -- ^Generalizer
  -- |Debug nodes
  | Prune a
  | Debug E.Gamma E.Sigma DGoal (Set.Set DGoal)

type DTree = DTree' DGoal

--

instance Show a => Show (DTree' a) where
  show Fail                        = "Fail"
  show (Success s                ) = "{Success}"
  show (Unfold  ts _ goal _          ) = "{Unfold \n [" ++ concatMap show ts ++ "]\n}"
  show (Abs ts _ goal _          ) = "{Abs \n [" ++ concatMap show ts ++ "]\n}"
  show (Gen t s                  ) = "{Gen  " ++ show t ++ "\n}"
  show (Renaming g _ _ _             ) = "{Renaming " ++ show g ++ "}"
  show (Prune d                  ) = "{Prune " ++ show d ++ "}"
  show (Debug env subst goal ancs) = "{Debug " ++ show goal ++ "}"

--
-- Return list of goals of tree's leaves (`Renaming` nodes)
--
leaves :: DTree -> [DGoal]
leaves (Unfold   ts _ _ _) = concatMap leaves ts
leaves (Abs  ts _ _ _) = concatMap leaves ts
leaves (Renaming g  _ _ _) = [g]
leaves (Gen t _      ) = leaves t
leaves _               = []

---

findVariantNode :: DGoal -> DTree -> Maybe DTree
findVariantNode dg n@(Unfold ts _ g _)
  | isVariant g dg = Just n
  | otherwise      = findFirst (findVariantNode dg) ts
findVariantNode dg n@(Abs ts _ g _)
  | isVariant g dg = Just n
  | otherwise      = findFirst (findVariantNode dg) ts
findVariantNode dg (Gen t _) = findVariantNode dg t
findVariantNode _  _         = Nothing

--
-- Match leaves' goals and nodes
--
matchVariants :: DTree -> [(DGoal, DTree)]
matchVariants t = fmap fromJust
  <$> filter (isJust . snd) ((,) <*> flip findVariantNode t <$> leaves t)

--
-- DTree to a set of goals of its nodes
--
treeGoals :: DTree -> Set.Set DGoal
treeGoals (Unfold  ts _ goal _) = Set.insert goal (Set.unions (treeGoals <$> ts))
treeGoals (Abs ts _ goal _) = Set.insert goal (Set.unions (treeGoals <$> ts))
treeGoals (Gen t _        ) = treeGoals t
treeGoals _                 = Set.empty

--
-- Evaluate tree's metrics.
--

--                    (leafs, Success, Fail)
countLeafs :: DTree -> (Int, Int, Int)
countLeafs (Unfold ts _ _ _) = foldl
  (\(n1, m1, h1) (n2, m2, h2) -> (n1 + n2, m1 + m2, h1 + h2))
  (0, 0, 0)
  (countLeafs <$> ts)
countLeafs (Abs ts _ _ _) = foldl
  (\(n1, m1, h1) (n2, m2, h2) -> (n1 + n2, m1 + m2, h1 + h2))
  (0, 0, 0)
  (countLeafs <$> ts)
countLeafs (Gen t _)   = countLeafs t
countLeafs Renaming{}      = (1, 0, 0)
countLeafs (Success _) = (0, 1, 0)
countLeafs Fail        = (0, 0, 1)
countLeafs _           = (0, 0, 0)

countDepth :: DTree -> Int
countDepth (Unfold  ts _ _ _) = 1 + foldl max 0 (countDepth <$> ts)
countDepth (Abs ts _ _ _) = 1 + foldl max 0 (countDepth <$> ts)
countDepth (Gen t _     ) = countDepth t
countDepth _              = 1

countNodes :: DTree -> Int
countNodes (Unfold  ts _ _ _) = 1 + sum (countNodes <$> ts)
countNodes (Abs ts _ _ _) = 1 + sum (countNodes <$> ts)
countNodes (Gen t _     ) = 1 + countNodes t
countNodes _              = 1

countPrunes :: DTree -> Int
countPrunes (Unfold  ts _ _ _) = sum (countPrunes <$> ts)
countPrunes (Abs ts _ _ _) = sum (countPrunes <$> ts)
countPrunes (Gen t _     ) = countPrunes t
countPrunes (Prune _     ) = 1
countPrunes _              = 0

-- Utils

findFirst f = getFirst . foldMap (First . f)
