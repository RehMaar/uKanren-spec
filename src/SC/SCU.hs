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
import           Data.List                     as List ( union, find )
import           Data.Foldable                            ( foldl' )
import           Control.Arrow (first)

import           Embedding

import           SC.DTreeZipper

import           PrettyPrint
import           Debug.Trace


-- |
toDTree :: UnfoldableGoal a => DTree' a -> DTree
toDTree Fail                   = Fail
toDTree (Success a           ) = Success a
toDTree (Renaming ugoal b) = Renaming (getGoal ugoal) b
toDTree (Gen a b             ) = Gen (toDTree a) b
toDTree (Unfold ts a ugoal) = Unfold (toDTree <$> ts) a (getGoal ugoal)
toDTree (Abs    ts a ugoal) = Abs (toDTree <$> ts) a (getGoal ugoal)


-- |Context of our algorithm execution.
newtype Context = Context
             { ctxEnv :: E.Env
             }

instance Show Context where
  show _ = "{context}"

-------------------------------------------------------------------------------

supercompUGen :: UnfoldableGoal a => SuperCompGen a
supercompUGen = supercompUUltraGen runZipper


supercompUGen2 :: UnfoldableGoal a => SuperCompGen a
supercompUGen2 = supercompUUltraGen runZipper2

supercompUUltraGen :: UnfoldableGoal a => (a -> E.Env -> DTreeZipper a) -> SuperCompGen a
supercompUUltraGen runZipper gl =
  let (goal, env, names) = goalXtoGoalS gl
      ug             = initGoal [goal]
  in (zipperToDTree $ runZipper ug env, goal, names)

-------------------------------------------------------------------------------


-- |Run a zipper to build a tree.
runZipper :: UnfoldableGoal a => a -> E.Env -> DTreeZipper a
runZipper goal env =
  let ctx = Context env
      zipper =
          (DTreeMultiNode (DTreeMulti UnfoldCon E.s0 goal) [], [])
  in  runner zipper ctx
  where
    runner :: UnfoldableGoal a => DTreeZipper a -> Context -> DTreeZipper a
    runner z ctx = case stepZipper z ctx of
      Nothing        -> z
      Just (z', ctx) -> runner z' ctx


runDebug n gl =
  let (goal, env, names) = goalXtoGoalS gl
      ug                 = initGoal [goal]
  in zipperToDTree $ runZipperN n ug env

-- |Make N steps.
runZipperN :: UnfoldableGoal a => Int -> a -> E.Env -> DTreeZipper a
runZipperN n goal env =
  let ctx = Context env
      zipper =
          (DTreeMultiNode (DTreeMulti UnfoldCon E.s0 goal) [], [])
  in  runnerN n zipper ctx
  where
    runnerN 0 z _ = z
    runnerN n z ctx = case stepZipper z ctx of
      Nothing -> z
      Just (z', ctx) -> runnerN (pred n) z' ctx

-------------------------------------------------------------------------------

-- |Get goals from `DTreeParent` type.
parentGoals :: UnfoldableGoal a => [DTreeParent a] -> [DGoal]
parentGoals [] = []
parentGoals (p : ps)
  | DTreeGenParent _ <- p      = parentGoals ps
  | DTreeMNodeParent nm _ <- p = getGoal (dtmGoal nm) : parentGoals ps

-- |Check if a zipper is focused on a particular node that can possibly be a parent.
isZipperOurParent parent zipper@(DTreeMultiNode mn _, _) = parent == getGoal (dtmGoal mn)
isZipperOurParent _ _ = False

-- |TODO
zipVars g = concatMap (uncurry mapVars) . zip g
  where
    goalVars :: DGoal -> [S]
    goalVars = foldr (List.union . invokeVars) []

    invokeVars :: G a -> [a]
    invokeVars (Invoke _ args) = concatMap getVars $ filter hasVars args

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

    mapTerms (V v1   ) v2        = [(v1, v2)]
    mapTerms (C _ ts1) (C _ ts2) = concatMap (uncurry mapTerms) $ zip ts1 ts2
    mapTerms t1 t2 = error ("Can't map terms <" ++ show t1 ++ "> and <" ++ show t2 ++ ">")

-- |To avoid repeatition of definitions we add links to the definitions instead of
-- repeated definition.
foldTree :: DTree -> DTree
foldTree = fst . foldTree' Set.empty
  where
    foldTree' :: Set.Set DGoal -> DTree -> (DTree, Set.Set DGoal)
    foldTree' seen (Unfold ts subst goal)
      | checkLeaf goal seen
      = (Renaming goal subst, seen)
      | otherwise
      = let (ts', seen') = foldl' (\(ts', seen) tree -> first (:ts') $ foldTree' seen tree) ([], Set.insert goal seen) ts
        in (Unfold (reverse ts') subst goal, seen')
    foldTree' seen (Abs ts subst goal)
      = let (ts', seen') = foldl' (\(ts', seen) tree -> first (:ts') $ foldTree' seen tree) ([], Set.insert goal seen) ts
        in (Abs (reverse ts') subst goal, seen')
    foldTree' seen (Gen t subst) = first (flip Gen subst) (foldTree' seen t)
    foldTree' s t = (t, s)

isUpwardGenP goal parent  = isStrictInst goal parent && not (isStrictInst parent goal)
isUpwardGen goal parents = any (isUpwardGenP goal) parents && not (null parents)

needUpwardGen :: UnfoldableGoal a => Set.Set DGoal -> E.Env -> DTreeMulti a -> Bool
needUpwardGen parents env (DTreeMulti AbsCon subst goal) = isUpwardGen (getGoal goal) parents
needUpwardGen _ _ _ = False

goalToTree
  :: UnfoldableGoal a =>
     Set.Set DGoal  -- |Parent nodes.
  -> E.Subst        -- |Substitution.
  -> a              -- |Goal.
  -> DTree' a
goalToTree parents subst goal
  | emptyGoal goal                     = Success subst
  | checkLeaf (getGoal goal) parents   = Renaming goal subst
  | isUpwardGen (getGoal goal) parents = Abs [] subst goal
  | whistle parents (getGoal goal)     = Abs [] subst goal
  | otherwise                          = Unfold [] subst goal

-------------------------------------------------------------------------------

stepZipper
  :: UnfoldableGoal a
  => DTreeZipper a
  -> Context
  -> Maybe (DTreeZipper a, Context)
stepZipper = stepZipper'
  where
    -- There's an option that we may want to do upward abstraction.
    stepZipper' zipper@(DTreeMultiNode mn [], parents) ctx
      | needUpwardGen parentSet (ctxEnv ctx) mn -- check isUpwardGen whisle
      , Just anc <- find (isUpwardGenP goal) parentList
      =
        let Just (parentNode, parents') = stepUntil goUp (isZipperOurParent anc) zipper
            varSubst = zipVars goal anc
            child = Unfold [] (parentSubst parentNode) (dtmGoal mn)
            genNode = Gen child varSubst
            node = parentNode{dtnChildren = [genNode]}
        in Just ((node, parents'), ctx)
      where parentSet = Set.fromList $ parentList
            parentList = parentGoals parents

            goal = getGoal $ dtmGoal mn

            parentSubst (DTreeMultiNode mn _) = dtmSubst mn
            parentSubst _ = error "stepZipper': wrong kind of node as a parent!"

    -- Empty <children> for MultiNode means that we need to fill it which possible children
    stepZipper' zipper@(DTreeMultiNode mn [], parents) ctx =
      let realGoal         = getGoal $ dtmGoal mn
          -- Now we have a lot of problems with this optimization, need to change the algorithm.
          -- seen             = Set.fromList $ getGoal <$> readyNodes zipper
          parentsList      = parentGoals parents
          -- First of all, need to generate nearest children of the node-in-focus
          (ctx', children) = generateChildren parentsList ctx mn
          -- And then focus on the most left one.
          newZipper        = goFirstChild (DTreeMultiNode mn children, parents)
      in  (, ctx') <$> newZipper
    -- If we are focused on GenNode we need just focus on its child
    stepZipper' zipper@(DTreeGenNode _ _, _) ctx = (, ctx) <$> goFirstChild zipper
    -- If we are focused on EndNode we need to go to the next child or up
    stepZipper' zipper@(DTreeEndNode _  , _) ctx = (, ctx) <$> goRightOrUp zipper
    -- Otherwise, if we are focused on MultiNode with children,
    -- then we know that either there's at least one child that has to be evaluated
    -- or all children are already evaluated and we need to go up.
    stepZipper' zipper@(DTreeMultiNode _ children, _) ctx
      | Just childZipper <- goNextChild zipper = Just (childZipper, ctx)
      | otherwise                              = (, ctx) <$> goUp zipper

    generateChildren
      :: forall a
       . UnfoldableGoal a
      => [DGoal]       -- | Parents
      -> Context       -- | Context
      -> DTreeMulti a  -- | Node in focus
      -> (Context, [DTree' a])
    -- If node is <Unfold> we need to unfold a goal and return newly created possibly unfinished subtrees.
    generateChildren ps ctx@(Context env) (DTreeMulti UnfoldCon subst goal) =
        case unfoldStep goal env subst of
        ([], _) -> (ctx, [Fail])
        -- uGoal :: [(E.Subst, UnfoldableGoal a)]
        (uGoals, nEnv) ->
          let parents = Set.fromList (getGoal goal : ps)
              trees = uncurry (goalToTree parents) <$> uGoals
          in  (ctx { ctxEnv = nEnv }, trees)
    generateChildren ps ctx@(Context env) (DTreeMulti AbsCon subst goal) =
      -- aGoals ::[(E.Subst, [G S], G.Generalizer)]
      let (aGoals, ns) = abstractFixed (Set.fromList ps) (getGoal goal) subst $ E.envNS env
          nEnv = env{E.envNS = ns}
          trees =
              (\(subst, nGoal, gen) ->
                  let parents = Set.fromList ps
                      tree = goalToTree parents subst (initGoal nGoal :: a) in
                  if null gen then tree else Gen tree gen
              ) <$> aGoals
      in  (ctx { ctxEnv = nEnv }, trees)

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
data Context2 = Context2
             { ctxEnv2 :: E.Env
             , ctxSeen :: Set.Set DGoal
             }

instance Show Context2 where
  show _ = "{context}"

runZipper2 goal env =
  let ctx = Context2 env Set.empty
      zipper =
          (DTreeMultiNode (DTreeMulti UnfoldCon E.s0 goal) [], [])
  in  runner zipper ctx
  where
    runner :: UnfoldableGoal a => DTreeZipper a -> Context2 -> DTreeZipper a
    runner z ctx = case stepZipper2 z ctx of
      Nothing        -> z
      Just (z', ctx) -> runner z' ctx

runDebug2 n gl =
  let (goal, env, names) = goalXtoGoalS gl
      ug                 = initGoal [goal]
  in zipperToDTree $ runZipper2N n ug env

runZipper2N n goal env =
  let ctx = Context2 env Set.empty
      zipper =
          (DTreeMultiNode (DTreeMulti UnfoldCon E.s0 goal) [], [])
  in  runnerN n zipper ctx
  where
    runnerN 0 z _ = z
    runnerN n z ctx = case stepZipper2 z ctx of
      Nothing -> z
      Just (z', ctx) -> runnerN (pred n) z' ctx

-- |Modification: renaming to seen nodes, not ony parents.
stepZipper2
  :: UnfoldableGoal a
  => DTreeZipper a
  -> Context2
  -> Maybe (DTreeZipper a, Context2)
stepZipper2 = stepZipper'
  where
    stepZipper' zipper@(DTreeMultiNode mn [], parents) ctx
      | needUpwardGen parentSet (ctxEnv2 ctx) mn
      , Just anc <- find (isUpwardGenP goal) parentList
      =
        let (Just (parentNode, parents')) = stepUntil goUp (isZipperOurParent anc) zipper
            varSubst = zipVars goal anc
            child = Unfold [] (parentSubst parentNode) (dtmGoal mn)
            genNode = Gen child varSubst
            node = parentNode{dtnChildren = [genNode]}
        in Just ((node, parents'), ctx{ctxSeen = Set.fromList $ getGoal <$> readyNodes (node, parents')})
      where
        parentSet = Set.fromList parentList
        parentList = parentGoals parents

        goal = getGoal $ dtmGoal mn

        parentSubst (DTreeMultiNode mn _) = dtmSubst mn
        parentSubst _ = error "stepZipper': wrong kind of node as a parent!"

    stepZipper' zipper@(DTreeMultiNode mn [], parents) ctx
      | checkLeaf (getGoal $ dtmGoal mn) (ctxSeen ctx)
      = let goal  = dtmGoal mn
            subst = dtmSubst mn
            env   = ctxEnv2 ctx
            parentSet = Set.fromList $ parentGoals parents
            node = RenamingEnd goal subst
            endZipper = (DTreeEndNode node, parents)
        in (, ctx) <$> goUp endZipper

    stepZipper' zipper@(DTreeMultiNode mn [], parents) ctx =
      let realGoal         = getGoal $ dtmGoal mn
          parentsList      = parentGoals parents
          ctx'             = ctx{ctxSeen = Set.insert realGoal $ ctxSeen ctx}
          (ctx'', children) = generateChildren parentsList ctx' mn
          newZipper        = goFirstChild (DTreeMultiNode mn children, parents)
      in  (, ctx'') <$> newZipper

    stepZipper' zipper@(DTreeGenNode _ _, _) ctx = (, ctx) <$> goFirstChild zipper
    stepZipper' zipper@(DTreeEndNode _  , _) ctx = (, ctx) <$> goRightOrUp zipper
    stepZipper' zipper@(DTreeMultiNode _ children, _) ctx
      | Just childZipper <- goNextChild zipper = Just (childZipper, ctx)
      | otherwise                              = (, ctx) <$> goUp zipper

    generateChildren :: forall a . UnfoldableGoal a =>
      [DGoal] -> Context2 -> DTreeMulti a -> (Context2, [DTree' a])
    generateChildren ps ctx@(Context2 env _) (DTreeMulti UnfoldCon subst goal) =
        -- trace ("Unfold: " ++ show goal ++ "\n") $
        case unfoldStep goal env subst of
        ([], _) -> (ctx, [Fail])
        -- uGoal :: [(E.Subst, UnfoldableGoal a)]
        (uGoals, nEnv) ->
          let parents = Set.fromList (getGoal goal : ps)
              trees = uncurry (goalToTree parents) <$> uGoals
          in  (ctx { ctxEnv2 = nEnv }, trees)
    generateChildren ps ctx@(Context2 env _) (DTreeMulti AbsCon subst goal) =
      -- aGoals ::[(E.Subst, [G S], G.Generalizer)]
      let (aGoals, ns) = abstractFixed (Set.fromList ps) (getGoal goal) subst $ E.envNS env
          nEnv = env{E.envNS = ns}
          trees =
              (\(subst, nGoal, gen) ->
                  let parents = Set.fromList ps
                      tree = goalToTree parents subst (initGoal nGoal :: a) in
                  if null gen then tree else Gen tree gen
              ) <$> aGoals
      in  (ctx { ctxEnv2 = nEnv }, trees)

isZipperRenaming :: UnfoldableGoal a => DTreeZipper a -> Bool
isZipperRenaming zipper@(DTreeMultiNode mn [], _) = checkLeaf (getGoal $ dtmGoal mn) (Set.fromList $ getGoal <$> readyNodes zipper)
isZipperRenaming _ = False
