{- Attemp to implement upward abstraction.

Upward abstraction occurs when a child term "t" is more general
than some of its parents (parent "p": p `embed` t).
-}

module SC.SCU where

import           Syntax
import           SC.DTree
import           SC.SC
import qualified Eval                          as E

import qualified Data.Set                      as Set
import           Data.List                     as List
                                                          ( union )
import           Data.Foldable                            ( foldl' )

import           Embedding

import           PrettyPrint
import           Debug.Trace

toDTree :: UnfoldableGoal a => DTree' a -> DTree
toDTree Fail                   = Fail
toDTree (Success a           ) = Success a
toDTree (Renaming ugoal b c d) = Renaming (getGoal ugoal) b c d
toDTree (Gen a b             ) = Gen (toDTree a) b
toDTree (Unfold ts a ugoal b ) = Unfold (toDTree <$> ts) a (getGoal ugoal) b
toDTree (Abs    ts a ugoal b ) = Abs (toDTree <$> ts) a (getGoal ugoal) b

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
                | SuccessEnd E.Sigma
                | RenamingEnd a (Set.Set DGoal) E.Sigma E.Gamma

instance Show (DTreeEnd a) where
  show FailEnd        = "FailEnd"
  show (SuccessEnd s) = "SuccessEnd"
  show RenamingEnd{}  = "LeadEnd"

endToNode :: DTreeEnd a -> DTree' a
endToNode FailEnd                = Fail
endToNode (SuccessEnd s        ) = Success s
endToNode (RenamingEnd d ds s g) = Renaming d ds s g

-- |Description of `Unfold` and `Abs` nodes
data MNodeType = UnfoldCon | AbsCon
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
 where
  tpFun UnfoldCon = Unfold
  tpFun AbsCon    = Abs

-- |Description of `Gen` node
type DTreeGen = E.Sigma

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
dTreeNode Fail                  = DTreeEndNode FailEnd
dTreeNode (Success s          ) = DTreeEndNode (SuccessEnd s)
dTreeNode (Renaming d  ds s g ) = DTreeEndNode (RenamingEnd d ds s g)
dTreeNode (Unfold cs s d ds)    = DTreeMultiNode (DTreeMulti UnfoldCon s d ds) cs
dTreeNode (Abs cs s  d ds)      = DTreeMultiNode (DTreeMulti AbsCon s d ds) cs
dTreeNode (Gen c s            ) = DTreeGenNode s c

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
isEmptyChild (Unfold [] _ _ _) = True
isEmptyChild (Abs    [] _ _ _) = True
isEmptyChild (Gen t _        ) = isEmptyChild t
isEmptyChild _                 = False

-- |Go upward.
goUp :: DTreeZipper a -> Maybe (DTreeZipper a)
goUp (c, (DTreeGenParent gen) : ps) =
  goUp (DTreeGenNode gen (nodeToDTree c), ps)
goUp (c, (DTreeMNodeParent mn childrenContext) : ps) =
  Just (DTreeMultiNode mn (zipperList (nodeToDTree c, childrenContext)), ps)
goUp _ = Nothing

-- |Go to the right child or upward.
goRightOrUp :: DTreeZipper a -> Maybe (DTreeZipper a)
goRightOrUp (c, DTreeGenParent gen : ps) =
  goUp (DTreeGenNode gen (nodeToDTree c), ps)
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

-- |Context of our algorithm execution.
newtype Context = Context
             { ctxEnv :: E.Gamma
             }

instance Show Context where
  show _ = "{context}"


supercompUGen :: UnfoldableGoal a => SuperCompGen a
supercompUGen gl =
  let (goal, env, names) = goalXtoGoalS gl
      ug             = initGoal [goal]
  in (zipperToDTree $ runZipper ug env, goal, names)

-- |Run a zipper to build a tree.
runZipper :: UnfoldableGoal a => a -> E.Gamma -> DTreeZipper a
runZipper goal env =
  let ctx = Context env
      zipper =
          (DTreeMultiNode (DTreeMulti UnfoldCon E.s0 goal Set.empty) [], [])
  in  runner zipper ctx

runZipper' :: UnfoldableGoal a => a -> E.Gamma -> (DTreeZipper a, Context)
runZipper' goal env =
  let ctx = Context env
      zipper =
          (DTreeMultiNode (DTreeMulti UnfoldCon E.s0 goal Set.empty) [], [])
  in  (,) zipper ctx

runner :: UnfoldableGoal a => DTreeZipper a -> Context -> DTreeZipper a
runner z ctx = case stepZipper z ctx of
  Nothing        -> z
  Just (z', ctx) -> runner z' ctx

-- |Get goals from `DTreeParent` type.
parentGoals :: UnfoldableGoal a => [DTreeParent a] -> [DGoal]
parentGoals [] = []
parentGoals (p : ps)
  | DTreeGenParent _ <- p      = parentGoals ps
  | DTreeMNodeParent nm _ <- p = getGoal (dtmGoal nm) : parentGoals ps

isZipperAnOurParent parent zipper@(DTreeMultiNode mn _, _) =
  parent == getGoal (dtmGoal mn)
isZipperAnOurParent _ _ = False

stepZipper
  :: UnfoldableGoal a
  => DTreeZipper a
  -> Context
  -> Maybe (DTreeZipper a, Context)
-- There's an option that we may want to do upward abstraction.
stepZipper zipper@(DTreeMultiNode mn [], parents) ctx
  | needUpwardGen parentSet ctx mn
  , Just anc <- findAncUpward goal parentSet
  = let (Just (parentNode, parents')) = stepUntil goUp (isZipperAnOurParent anc) zipper
        varSubst = zipVars goal anc
        child = Unfold [] (parentSubst parentNode) (dtmGoal mn) parentSet
        node = DTreeGenNode varSubst child
    in Just ((node, parents'), ctx)
  where parentSet = Set.fromList $ parentGoals parents

        goal = getGoal $ dtmGoal mn

        parentSubst (DTreeMultiNode mn _) = dtmSubst mn
        parentSubst _ = error "stepZipper: wrong kind of node as a parent!"

-- Empty <children> for MultiNode means that we need to fill it which possible children
stepZipper (DTreeMultiNode mn [], parents) ctx =
  let realGoal         = getGoal $ dtmGoal mn
      -- First of all, need to generate nearest children of the node-in-focus
      (ctx', children) = generateChildren (parentGoals parents) ctx mn
      -- And then focus on the most left one.
      newZipper        = goFirstChild (DTreeMultiNode mn children, parents)
  in  (, ctx') <$> newZipper
-- If we are focused on GenNode we need just focus on its child
stepZipper zipper@(DTreeGenNode _ _, _) ctx = (, ctx) <$> goFirstChild zipper
-- If we are focused on EndNode we need to go to the next child or up
stepZipper zipper@(DTreeEndNode _  , _) ctx = (, ctx) <$> goRightOrUp zipper
-- Otherwise, if we are focused on MultiNode with children,
-- then we know that either there's at least one child that has to be evaluated
-- or all children are already evaluated and we need to go up.
stepZipper zipper@(DTreeMultiNode _ children, _) ctx
  | Just childZipper <- goNextChild zipper = Just (childZipper, ctx)
  | otherwise                              = (, ctx) <$> goUp zipper

needUpwardGen
  :: UnfoldableGoal a => Set.Set DGoal -> Context -> DTreeMulti a -> Bool
needUpwardGen parents ctx@(Context env) (DTreeMulti AbsCon subst goal _) =
  let abs = abstract parents (getGoal goal) subst env
  in  abstractSame abs (getGoal goal)
needUpwardGen _ _ _ = False

generateChildren
  :: forall a
   . UnfoldableGoal a
  => [DGoal]       -- | Parents
  -> Context       -- | Context
  -> DTreeMulti a  -- | Node in focus
  -> (Context, [DTree' a])
-- If node is <Unfold> we need to unfold a goal and return newly created possibly unfinished subtrees.
generateChildren ps ctx@(Context env) (DTreeMulti UnfoldCon subst goal _) =
  case unfoldStep goal env subst of
    ([], _) -> (ctx, [Fail])
    -- uGoal :: [(E.Sigma, UnfoldableGoal a)]
    (uGoals, nEnv) ->
      let trees = uncurry (goalToTree (getGoal goal : ps) nEnv) <$> uGoals
      in  (ctx { ctxEnv = nEnv }, trees)
generateChildren ps ctx@(Context env) (DTreeMulti AbsCon subst goal _) =
  -- aGoals ::[(E.Sigma, [G S], G.Generalizer)]
  let (aGoals, nEnv) = abstractFixed (Set.fromList ps) (getGoal goal) subst env
      trees =
          (\(subst, nGoal, gen) ->
              let tree = goalToTree ps nEnv subst (initGoal nGoal :: a) in
              if null gen then tree else Gen tree gen
          ) <$> aGoals
  in  (ctx { ctxEnv = nEnv }, trees)


goalToTree :: UnfoldableGoal a => [DGoal] -> E.Gamma -> E.Sigma -> a -> DTree' a
goalToTree parents env subst goal
  | emptyGoal goal                      = Success subst
  | checkLeaf (getGoal goal) parentsSet = Renaming goal parentsSet subst env
  | isGen (getGoal goal) parentsSet     = Abs [] subst goal parentsSet
  | otherwise                           = Unfold [] subst goal parentsSet
  where parentsSet = Set.fromList parents
        {- Want to leave original parents now -}

goalVars :: DGoal -> [S]
goalVars = foldr (List.union . invokeVars) []
  where
    invokeVars :: G a -> [a]
    invokeVars (Invoke _ args) = concatMap getVars $ filter hasVars args
     where
      getVars (V i   ) = [i]
      getVars (C _ ts) = concatMap getVars ts

      hasVars (V _   ) = True
      hasVars (C _ ts) = any hasVars ts && not (null ts)

mapVars i1@(Invoke n1 a1) i2@(Invoke n2 a2)
  | n1 == n2
  , length a1 == length a2
  = concatMap (uncurry mapTerms) $ zip a1 a2
  | otherwise
  = error $ "Can't map variables of invokes <" ++ show i1 ++ "> and <" ++ show i2 ++ ">"
 where
  mapTerms (V v1   ) v2        = [(v1, v2)]
  mapTerms (C _ ts1) (C _ ts2) = concatMap (uncurry mapTerms) $ zip ts1 ts2
  mapTerms t1 t2 =
    error ("Can't map terms <" ++ show t1 ++ "> and <" ++ show t2 ++ ">")

zipVars g = concatMap (uncurry mapVars) . zip g
