{- Attemp to implement upward abstraction.

Upward abstraction occurs when a child term "t" is more general
than some of its parents (parent "p": p `embed` t).
-}

module SC.SCU where

import Syntax
import SC.DTree
import SC.SC
import qualified Eval as E

import qualified Data.Set as Set
import Data.Foldable (foldl')

import PrettyPrint
import Debug.Trace

toDTree :: UnfoldableGoal a => DTree' a -> DTree
toDTree Fail = Fail
toDTree (Success a) = Success a
toDTree (Leaf ugoal b c d) = Leaf (getGoal ugoal) b c d
toDTree (Gen a b) = Gen (toDTree a) b
toDTree (Or ts a ugoal b) = Or (toDTree <$> ts) a (getGoal ugoal) b
toDTree (And ts a ugoal b) = And (toDTree <$> ts) a (getGoal ugoal) b

type ListContext a = ([a], [a]) 

type ListZipper a = (a, ListContext a)

listZipper :: [a] -> Maybe (ListZipper a)
listZipper (x:xs) = Just (x, ([], xs))
listZipper _ = Nothing

lzLeft :: ListZipper a -> Maybe (ListZipper a)
lzLeft (y, (x':xs, ys)) = Just (x', (xs, y:ys))
lzLeft _ = Nothing

lzRight :: ListZipper a -> Maybe (ListZipper a)
lzRight (x, (xs, y:ys)) = Just (y, (x:xs, ys))
lzRight _ = Nothing

zipperList :: ListZipper a -> [a]
zipperList ~(y, (xs, ys)) = foldl' (flip (:)) (y:ys) xs

lzShiftUntil :: (a -> Bool) -> ListZipper a -> Maybe (ListZipper a)
lzShiftUntil p ~zipper@(c, _)
  | p c
  = Just $ zipper
  | otherwise
  = lzRight zipper >>= \z -> lzShiftUntil p z

data DTreeEnd a = FailEnd
                | SuccessEnd E.Sigma
                | LeafEnd a (Set.Set DGoal) E.Sigma E.Gamma

instance Show (DTreeEnd a) where
  show FailEnd = "FailEnd"
  show (SuccessEnd s) = "SuccessEnd"
  show (LeafEnd _ _ _ _) = "LeadEnd"

endToNode :: DTreeEnd a -> DTree' a
endToNode FailEnd            = Fail
endToNode (SuccessEnd s)     = Success s
endToNode (LeafEnd d ds s g) = Leaf d ds s g

data MNodeType = OrCon | AndCon
  deriving Show
data DTreeMulti a = DTreeMulti
                  { dtmMnodeType :: MNodeType
                  , dtmSubst     :: E.Sigma
                  , dtmGoal      :: a
                  , dtmParents   :: Set.Set DGoal
                  }
  deriving Show

mnodeToNode :: DTreeMulti a -> [DTree' a] -> DTree' a
mnodeToNode (DTreeMulti typ s d ds) children = tpFun typ children s d ds
    where tpFun OrCon  = Or
          tpFun AndCon = And

type DTreeGen = E.Sigma

data DTreeParent a = DTreeMNodeParent { dtpNode :: DTreeMulti a, dtpChildren :: ListContext (DTree' a) }
                   | DTreeGenParent   { dtpGen :: DTreeGen }
  deriving Show

data DTreeNode a = DTreeEndNode   { dtnEndNode :: DTreeEnd a }
                 | DTreeMultiNode { dtnMultiNode :: DTreeMulti a, dtnChildren :: [DTree' a] }
                 | DTreeGenNode   { dtnGen :: DTreeGen, dtnChild :: DTree' a }
  deriving Show

nodeToDTree (DTreeEndNode end) = endToNode end
nodeToDTree (DTreeMultiNode mnode children) = mnodeToNode mnode children
nodeToDTree (DTreeGenNode gen t) = Gen t gen

type DTreeZipper a = (DTreeNode a, [DTreeParent a])

parents :: DTreeZipper a -> [DTreeParent a]
parents = snd

dTreeNode :: DTree' a -> DTreeNode a
dTreeNode Fail            = DTreeEndNode FailEnd
dTreeNode (Success s)     = DTreeEndNode (SuccessEnd s)
dTreeNode (Leaf d ds s g) = DTreeEndNode (LeafEnd d ds s g)
dTreeNode (Or cs s d ds)  = DTreeMultiNode (DTreeMulti OrCon s d ds) cs
dTreeNode (And cs s d ds) = DTreeMultiNode (DTreeMulti AndCon s d ds) cs
dTreeNode (Gen c s)       = DTreeGenNode s c

dTreeZipper parents dtree = (dTreeNode dtree, parents)

goFirstChild :: DTreeZipper a -> Maybe (DTreeZipper a)
goFirstChild (DTreeEndNode _, _)       = Nothing
goFirstChild (DTreeMultiNode dc cs, p) = do (c, lz) <- listZipper cs
                                            pure $ dTreeZipper (DTreeMNodeParent dc lz : p) c
goFirstChild (DTreeGenNode s c, p)     = Just $ dTreeZipper (DTreeGenParent s : p) c

goNextChild :: DTreeZipper a -> Maybe (DTreeZipper a)
goNextChild (DTreeEndNode _, _)       = Nothing
goNextChild (DTreeMultiNode dc cs, p) = do zipper <- listZipper cs
                                           (child, lzCtx) <- lzShiftUntil isEmptyChild zipper
                                           pure $ dTreeZipper (DTreeMNodeParent dc lzCtx : p) child
goNextChild (DTreeGenNode s c, p)     = Just $ dTreeZipper (DTreeGenParent s : p) c

isEmptyChild :: DTree' a -> Bool
isEmptyChild (Or [] _ _ _)  = True
isEmptyChild (And [] _ _ _) = True
isEmptyChild (Gen t _)      = isEmptyChild t
isEmptyChild _              = False

zipperToDTree :: DTreeZipper a -> DTree' a
zipperToDTree zipper = foldl' parentToDTree (nodeToDTree (fst zipper)) (parents zipper)
  where
    parentToDTree tree (DTreeGenParent gen)        = Gen tree gen
    parentToDTree tree (DTreeMNodeParent mnode lz) = let children = zipperList (tree, lz) in mnodeToNode mnode children

goUp :: DTreeZipper a -> Maybe (DTreeZipper a)
goUp (c, (DTreeGenParent gen):ps) = goUp (DTreeGenNode gen (nodeToDTree c), ps)
goUp (c, (DTreeMNodeParent mn childrenContext):ps) = Just (DTreeMultiNode mn (zipperList (nodeToDTree c, childrenContext)), ps)
goUp _ = Nothing

goRightOrUp :: DTreeZipper a -> Maybe (DTreeZipper a)
goRightOrUp (c, DTreeGenParent gen:ps) = goUp (DTreeGenNode gen (nodeToDTree c), ps)
goRightOrUp (c, DTreeMNodeParent mn childrenContext:ps)
  | Just (nc, newChildrenContext) <- lzRight lz
  = Just (dTreeNode nc, DTreeMNodeParent mn newChildrenContext:ps)
  | otherwise
  = Just (DTreeMultiNode mn (zipperList lz), ps)
  where lz = (nodeToDTree c, childrenContext)
goRightOrUp _ = Nothing


farthest :: (a -> Maybe a) -> a -> a
farthest f a = maybe a (farthest f) (f a)

stepUntil :: (a -> Maybe a) -> (a -> Bool) -> a -> Maybe a
stepUntil step p zipper
  | p zipper
  = Just zipper
  | otherwise
  = step zipper >>= stepUntil step p

data Context = Context
             { ctxEnv :: E.Gamma
             }

instance Show Context where
  show _ = "{context}"

runnest gl = let
  (goal, env, _) = goalXtoGoalS gl
  ug = initGoal [goal]
  in run ug env

run :: UnfoldableGoal a => a -> E.Gamma -> DTreeZipper a
run goal env = let
  ctx = Context env
  zipper = (DTreeMultiNode (DTreeMulti OrCon E.s0 goal Set.empty) [], [])
  in f zipper ctx

run' :: UnfoldableGoal a => a -> E.Gamma -> (DTreeZipper a, Context)
run' goal env = let
  ctx = Context env
  zipper = (DTreeMultiNode (DTreeMulti OrCon E.s0 goal Set.empty) [], [])
  in (,) zipper ctx

f :: UnfoldableGoal a => DTreeZipper a -> Context -> DTreeZipper a
f z ctx = case stepZipper z ctx of
            Nothing -> z
            Just (z', ctx) -> f z' ctx

parentGoals :: UnfoldableGoal a => [DTreeParent a] -> [DGoal]
parentGoals [] = []
parentGoals (p:ps)
  | DTreeGenParent _ <- p
  = parentGoals ps
  | DTreeMNodeParent nm _ <- p
  = getGoal (dtmGoal nm) : parentGoals ps

isZipperAnOurParent parent zipper@(DTreeMultiNode mn _, _) = parent == getGoal (dtmGoal mn)
isZipperAnOurParent _ _ = False

stepZipper :: UnfoldableGoal a => DTreeZipper a -> Context -> Maybe (DTreeZipper a, Context)
-- There's an option that we may want to do upward abstraction.
--
{-stepZipper zipper@(DTreeMultiNode mn [], parents) ctx
  | needUpwardGen (Set.fromList $ parentGoals parents) ctx mn
  , Just anc <- findAncUpward (getGoal $ dtmGoal mn) (Set.fromList $ parentGoals parents)
  =
    trace ("Upward: " ++ show (getGoal $ dtmGoal mn) ++ "\nAnc: " ++ show anc) $
    let (Just (_, parents')) = stepUntil goUp (isZipperAnOurParent anc) zipper
    in Just ((DTreeMultiNode mn{dtmMnodeType = OrCon} [], parents'), ctx)-}
-- Empty <children> for MultiNode means that we need to fill it which possible children
stepZipper (DTreeMultiNode mn [], parents) ctx = let
  realGoal = getGoal $ dtmGoal mn
  -- First of all, need to generate nearest children of the node-in-focus
  (ctx', children) = generateChildren (parentGoals parents) ctx mn
  -- And then focus on the most left one.
  newZipper = goFirstChild (DTreeMultiNode mn children, parents)
  in (, ctx') <$> newZipper
-- If we are focused on GenNode we need just focus on its child
stepZipper zipper@(DTreeGenNode _ _, _) ctx = (, ctx) <$> goFirstChild zipper
-- If we are focused on EndNode we need to go to the next child or up
stepZipper zipper@(DTreeEndNode _, _) ctx = (, ctx) <$> goRightOrUp zipper
-- Otherwise, if we are focused on MultiNode with children,
-- then we know that either there's at least one child that has to be evaluated
-- or all children are already evaluated and we need to go up.
stepZipper zipper@(DTreeMultiNode _ children, _) ctx
  | Just childZipper <- goNextChild zipper
  = Just (childZipper, ctx)
  | otherwise
  = (,ctx) <$> goUp zipper

needUpwardGen :: UnfoldableGoal a => Set.Set DGoal -> Context -> DTreeMulti a -> Bool
needUpwardGen parents ctx@(Context env) (DTreeMulti AndCon subst goal _) =
   let abs = abstract parents (getGoal goal) subst env
   in abstractSame abs (getGoal goal)
needUpwardGen _ _ _ = False

generateChildren :: forall a. UnfoldableGoal a =>
     [DGoal]       -- | Parents
  -> Context       -- | Context
  -> DTreeMulti a  -- | Node in focus
  -> (Context, [DTree' a])
-- If node is <Or> we need to unfold a goal and return newly created possibly unfinished subtrees.
generateChildren ps ctx@(Context env) (DTreeMulti OrCon subst goal _) =
  case unfoldStep goal env subst of
     ([], _)        -> (ctx, [Fail])
     -- uGoal :: [(E.Sigma, UnfoldableGoal a)]
     (uGoals, nEnv) ->
       let trees = uncurry (goalToTree (getGoal goal : ps) nEnv) <$> uGoals
       in (ctx{ctxEnv = nEnv}, trees)
generateChildren ps ctx@(Context env) (DTreeMulti AndCon subst goal _) =
  -- aGoals ::[(E.Sigma, [G S], G.Generalizer)]
  let (aGoals, nEnv) = abstractFixed (Set.fromList ps) (getGoal goal) subst env
      trees = (\(subst, nGoal, gen) -> Gen (goalToTree ps nEnv subst $ (initGoal nGoal :: a)) gen) <$> aGoals
  in (ctx{ctxEnv = nEnv}, trees)


goalToTree :: UnfoldableGoal a => [DGoal] -> E.Gamma -> E.Sigma -> a -> DTree' a
goalToTree parents env subst goal
  | emptyGoal goal
  = Success subst
  | checkLeaf (getGoal goal) parentsSet
  = Leaf goal parentsSet subst env
  | isGen (getGoal goal) parentsSet
  -- Need to check it until we completly add upward abstraction
  , abs <- abstract parentsSet (getGoal goal) subst env
  , not $ abstractSame abs (getGoal goal)
  = And [] subst goal parentsSet
{-  | isUpwardGen (getGoal goal) parentsSet
  = And [] subst goal parentsSet
-}
  | otherwise
  = Or [] subst goal parentsSet
  where parentsSet = Set.fromList parents
        {- Want to leave original parents -}
