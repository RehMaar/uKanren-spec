{- Attemp to implement upward abstraction.

Upward abstraction occurs when a child term "t" is more general
than some of its parents (parent "p": p `embed` t).
-}

module SC.DTreeZipper where

import           Syntax
import           SC.DTree
import           SC.SC
import qualified Eval                          as E

import qualified Data.Set                      as Set
import           Data.List                     as List ( union, find )
import           Data.Foldable                            ( foldl' )
import           Control.Arrow (first)

import           Embedding

import           PrettyPrint
import           Debug.Trace

-- |List Zipper

type ListContext a = ([a], [a])

type ListZipper a = (a, ListContext a)

listZipper :: [a] -> Maybe (ListZipper a)
listZipper (x : xs) = Just (x, ([], xs))
listZipper _        = Nothing

lzLeft :: ListZipper a -> Maybe (ListZipper a)
lzLeft (y, (x' : xs, ys)) = Just (x', (xs, y : ys))
lzLeft _                  = Nothing

lzRight :: ListZipper a -> Maybe (ListZipper a)
lzRight (x, (xs, y : ys)) = Just (y, (x : xs, ys))
lzRight _                 = Nothing

zipperList :: ListZipper a -> [a]
zipperList ~(y, (xs, ys)) = foldl' (flip (:)) (y : ys) xs

lzShiftUntil :: (a -> Bool) -> ListZipper a -> Maybe (ListZipper a)
lzShiftUntil p ~zipper@(c, _)
  | p c       = Just zipper
  | otherwise = lzRight zipper >>= \z -> lzShiftUntil p z

-- |Tree Zipper

-- |Leaf nodes description
data DTreeEnd a = FailEnd
                | SuccessEnd E.Subst E.ConstrStore
                | RenamingEnd a E.Subst E.ConstrStore

instance Show (DTreeEnd a) where
  show FailEnd        = "FailEnd"
  show SuccessEnd{} = "SuccessEnd"
  show RenamingEnd{}  = "RenamingEnd"

endToNode :: DTreeEnd a -> DTree' a
endToNode FailEnd           = Fail
endToNode (SuccessEnd s c)  = Success s c
endToNode (RenamingEnd d s c) = Renaming d s c

-- |Description of `Unfold` and `Abs` nodes
data MNodeType = UnfoldCon | AbsCon
  deriving Show


data DTreeMulti a = DTreeMulti
                  { dtmMnodeType :: MNodeType
                  , dtmSubst     :: E.Subst
                  , dtmCStore    :: E.ConstrStore
                  , dtmGoal      :: a
                  }
  deriving Show

mnodeToNode :: DTreeMulti a -> [DTree' a] -> DTree' a
mnodeToNode (DTreeMulti typ s c d) children = tpFun typ children s c d
 where
  tpFun UnfoldCon = Unfold
  tpFun AbsCon    = Abs

-- |Description of `Gen` node
type DTreeGen = E.Subst

-- |Context for all possible parent nodes.
data DTreeParent a = DTreeMNodeParent { dtpMNode :: DTreeMulti a, dtpChildren :: ListContext (DTree' a) }
                  -- ^MultiNode Parenthood.
                  -- Stores the rest of its children with a hole for a currently focused one.
                   | DTreeGenParent   { dtpGen :: DTreeGen }
                  -- ^Gen Parenthood.
  deriving Show

-- |Tree Context. Describes focused node.
data DTreeNode a = DTreeEndNode   { dtnEndNode :: DTreeEnd a }
                 | DTreeMultiNode { dtnMultiNode :: DTreeMulti a, dtnChildren :: [DTree' a] }
                 | DTreeGenNode   { dtnGen :: DTreeGen, dtnChild :: DTree' a }
  deriving Show

nodeToDTree (DTreeEndNode end             ) = endToNode end
nodeToDTree (DTreeMultiNode mnode children) = mnodeToNode mnode children
nodeToDTree (DTreeGenNode   gen   t       ) = Gen t gen

-- |Tree Zipper: a focused node and its context (all their parents).
type DTreeZipper a = (DTreeNode a, [DTreeParent a])

parents :: DTreeZipper a -> [DTreeParent a]
parents = snd

-- | Focus on a node
dTreeNode :: DTree' a -> DTreeNode a
dTreeNode Fail            = DTreeEndNode FailEnd
dTreeNode (Success s c  ) = DTreeEndNode (SuccessEnd s c)
dTreeNode (Renaming d s c) = DTreeEndNode (RenamingEnd d s c)
dTreeNode (Unfold cs s c d) = DTreeMultiNode (DTreeMulti UnfoldCon s c d) cs
dTreeNode (Abs cs s c d)   = DTreeMultiNode (DTreeMulti AbsCon s c d) cs
dTreeNode (Gen c s      ) = DTreeGenNode s c

-- | Create a zipper
dTreeZipper parents dtree = (dTreeNode dtree, parents)

-- |Convert a zipper to a tree
zipperToDTree :: DTreeZipper a -> DTree' a
zipperToDTree zipper = foldl' parentToDTree
                              (nodeToDTree (fst zipper))
                              (parents zipper)
 where
  parentToDTree tree (DTreeGenParent gen) = Gen tree gen
  parentToDTree tree (DTreeMNodeParent mnode lz) =
    let children = zipperList (tree, lz) in mnodeToNode mnode children

-- |Return a set of already met and fully evaluated nodes.
-- Such nodes are current node's parents left children.
readyNodes :: DTreeZipper a -> [a]
readyNodes (_, parents) = concatMap ready' parents
  where
    ready' (DTreeMNodeParent mn children) = dtmGoal mn : readyLC children
    ready' (DTreeGenParent _) = []

    readyLC :: ListContext (DTree' a) -> [a]
    readyLC (c, _) = concatMap readyInTree c

    readyInTree :: DTree' a -> [a]
    readyInTree (Unfold ts _ _ gl) = gl : concatMap readyInTree ts
    readyInTree (Abs ts _ _ gl) = gl : concatMap readyInTree ts
    readyInTree (Gen t _) = readyInTree t
    readyInTree (Renaming gl _ _) = [gl]
    readyInTree _ = []

-- |Zipper walkers

-- |Go to the most left child if possible.
goFirstChild :: DTreeZipper a -> Maybe (DTreeZipper a)
goFirstChild (DTreeEndNode _      , _) = Nothing
goFirstChild (DTreeMultiNode dc cs, p) = do
  (c, lz) <- listZipper cs
  pure $ dTreeZipper (DTreeMNodeParent dc lz : p) c
goFirstChild (DTreeGenNode s c, p) =
  Just $ dTreeZipper (DTreeGenParent s : p) c

-- |Go to the next (in the list zipper order) child if possible.
goNextChild :: DTreeZipper a -> Maybe (DTreeZipper a)
goNextChild (DTreeEndNode _      , _) = Nothing
goNextChild (DTreeMultiNode dc cs, p) = do
  zipper         <- listZipper cs
  (child, lzCtx) <- lzShiftUntil isEmptyChild zipper
  pure $ dTreeZipper (DTreeMNodeParent dc lzCtx : p) child
goNextChild (DTreeGenNode s c, p) = Just $ dTreeZipper (DTreeGenParent s : p) c

isEmptyChild :: DTree' a -> Bool
isEmptyChild (Unfold [] _ _ _ ) = True
isEmptyChild (Abs    [] _ _ _ ) = True
isEmptyChild (Gen t _       ) = isEmptyChild t
isEmptyChild _                = False

-- |Go upward.
goUp :: DTreeZipper a -> Maybe (DTreeZipper a)
goUp (c, (DTreeGenParent gen) : ps)
  = goUp (DTreeGenNode gen (nodeToDTree c), ps)
goUp (c, (DTreeMNodeParent mn childrenContext) : ps)
  = Just (DTreeMultiNode mn (zipperList (nodeToDTree c, childrenContext)), ps)
goUp _ = Nothing

-- |Go to the right child or upward.
goRightOrUp :: DTreeZipper a -> Maybe (DTreeZipper a)
goRightOrUp (c, DTreeGenParent gen : ps)
  = goUp (DTreeGenNode gen (nodeToDTree c), ps)
goRightOrUp (c, DTreeMNodeParent mn childrenContext : ps)
  | Just (nc, newChildrenContext) <- lzRight lz = Just
    (dTreeNode nc, DTreeMNodeParent mn newChildrenContext : ps)
  | otherwise = Just (DTreeMultiNode mn (zipperList lz), ps)
  where lz = (nodeToDTree c, childrenContext)
goRightOrUp _ = Nothing

-- | Take a step until a `predicate`.
stepUntil :: (a -> Maybe a) -> (a -> Bool) -> a -> Maybe a
stepUntil step p zipper | p zipper  = Just zipper
                        | otherwise = step zipper >>= stepUntil step p
