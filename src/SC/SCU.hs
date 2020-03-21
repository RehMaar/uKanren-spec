{- Attemp to implement upward abstraction. -}
module SC.SCU where

import SC.DTree
import qualified Eval as E
import qualified Data.Set as Set
import Data.Foldable (foldl')

type ListContext a = ([a], [a]) 

type ListZipper a = (a, ListContext a)

listZipper :: [a] -> Maybe (ListZipper a)
listZipper (x:xs) = Just (x, (xs, []))
listZipper _ = Nothing

lzLeft :: ListZipper a -> Maybe (ListZipper a)
lzLeft (y, (x':xs, ys)) = Just (x', (xs, y:ys))
lzLeft _ = Nothing

lzRight :: ListZipper a -> Maybe (ListZipper a)
lzRight (x, (xs, y:ys)) = Just (y, (x:xs, ys))
lzRight _ = Nothing

zipperList :: ListZipper a -> [a]
zipperList ~(y, (xs, ys)) = foldl' (flip (:)) (y:ys) xs

data DTreeEnd = FailEnd
              | SuccessEnd E.Sigma
              | LeafEnd DGoal (Set.Set DGoal) E.Sigma E.Gamma

endToNode :: DTreeEnd -> DTree
endToNode FailEnd            = Fail
endToNode (SuccessEnd s)     = Success s
endToNode (LeafEnd d ds s g) = Leaf d ds s g

data MNodeType = OrCon | AndCon
data DTreeMNode = DTreeMNode MNodeType E.Sigma DGoal (Set.Set DGoal)

mnodeToNode :: DTreeMNode -> [DTree] -> DTree
mnodeToNode (DTreeMNode typ s d ds) children = tpFun typ children s d ds
    where tpFun OrCon  = Or
          tpFun AndCon = And

type DTreeGen = E.Sigma

data DTreeParent = DTreeMNodeParent DTreeMNode (ListContext DTree)
                 | DTreeGenParent DTreeGen

data DTreeNode = DTreeEndNode DTreeEnd
               | DTreeMNodeNode DTreeMNode [DTree]
               | DTreeGenNode DTreeGen DTree

nodeToDTree (DTreeEndNode end) = endToNode end
nodeToDTree (DTreeMNodeNode mnode children) = mnodeToNode mnode children
nodeToDTree (DTreeGenNode gen t) = Gen t gen

type DTreeZipper = (DTreeNode, [DTreeParent])

parents :: DTreeZipper -> [DTreeParent]
parents = snd

dTreeNode :: DTree -> DTreeNode
dTreeNode Fail            = DTreeEndNode FailEnd
dTreeNode (Success s)     = DTreeEndNode (SuccessEnd s)
dTreeNode (Leaf d ds s g) = DTreeEndNode (LeafEnd d ds s g)
dTreeNode (Or cs s d ds)  = DTreeMNodeNode (DTreeMNode OrCon s d ds) cs
dTreeNode (And cs s d ds) = DTreeMNodeNode (DTreeMNode AndCon s d ds) cs
dTreeNode (Gen c s)       = DTreeGenNode s c

dTreeZipper parents dtree = (dTreeNode dtree, parents)

goFirstChild :: DTreeZipper -> Maybe DTreeZipper
goFirstChild (DTreeEndNode _, _)       = Nothing
goFirstChild (DTreeMNodeNode dc cs, p) = do (c, lz) <- listZipper cs
                                            pure $ dTreeZipper (DTreeMNodeParent dc lz : p) c
goFirstChild (DTreeGenNode s c, p)     = Just $ dTreeZipper (DTreeGenParent s : p) c

zipperToDTree :: DTreeZipper -> DTree
zipperToDTree zipper = foldl' parentToDTree (nodeToDTree (fst zipper)) (parents zipper)
  where
    parentToDTree :: DTree -> DTreeParent -> DTree
    parentToDTree tree (DTreeGenParent gen) = Gen tree gen
    parentToDTree tree (DTreeMNodeParent mnode lz) = let children = zipperList (tree, lz) in mnodeToNode mnode children

-- f :: Zipper -> Zipper
-- f z = case stepZipper z of
--         Nothing -> z
--         Just z' -> f z'
