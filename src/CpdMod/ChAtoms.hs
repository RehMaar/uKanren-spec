{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections, InstanceSigs #-}

module CpdMod.ChAtoms where
    
import CPD
import Embedding
import Syntax
import qualified Eval as E
import qualified Driving as D
import Utils (zipBy, subconjs)
import           Purification

import Data.List
import Data.Maybe
import qualified Data.Map.Strict as Map
import qualified Control.Arrow as A ((&&&), (***), first, second)
import qualified Data.Set                      as Set
import Debug.Trace

--
-- For CPD atom can be a conj of goals.
--
type Atom a = [G a]

msgAtom :: E.Delta -> [Atom S] -> (Atom S, E.Delta)
msgAtom _ [] = error "msg on empty list"
msgAtom dlt as = foldr (\g (a, dlt') -> f $ D.generalizeGoals dlt' g a) (head as, dlt) (tail as)
  where f (g, _, _, dlt') = (g, dlt')


--
-- Atom position in the goal.
--
type AtomPos = Int

--
-- Clause used for unfolding.
--
type ClauseNum = Int

--
-- Inner representation of SLD Tree containing
-- information about derivation structure to build the
-- characteristic tree of the derivation.
--
data SldTreeInner = FFail
                  | SSuccess E.Sigma AtomPos
                  | OOr [(ClauseNum, SldTreeInner)] E.Sigma
                  | CConj SldTreeInner [DescendGoal] E.Sigma AtomPos
                  | LLeaf [DescendGoal] E.Sigma E.Gamma

instance Show SldTreeInner where
    show FFail = "Fail"
    show (SSuccess s i) = "Success (" ++ show i ++ ") " ++ show s
    show (OOr ss s) = "Or {\n  " ++ show ss ++ "\n  " ++ show s ++ "\n}"
    show (CConj sld dg s i) = "Conj (" ++ show i ++ ") {" ++ show sld ++ " " ++ show dg ++ " " ++ show s ++ "}"
    show (LLeaf dgs d gm) = "Leaf {" ++ show dgs ++ " " ++ show d ++ " " ++ showG gm ++ "}"
      where showG (p, i, d) = "Gamma"


innerToSld :: SldTreeInner -> SldTree
innerToSld FFail             = Fail
innerToSld (SSuccess s  _  ) = Success s
innerToSld (OOr      ct s  ) = Or ((innerToSld . snd) <$> ct) s
innerToSld (CConj sld d s _) = Conj (innerToSld sld) d s
innerToSld (LLeaf dg s g   ) = Leaf dg s g


type ChStep = (AtomPos, ClauseNum)

type ChPath = [ChStep]

--
-- Characteristic tree is the set of characteristic paths
-- of the non-failing derivations of the incomplete SLD-tree.
--
-- Characteristic path of the derivation is the sequence of (l_i, c_i)
-- where l_i is the position of the selected literal and c_i is the
-- number of the clause chosen to resolve with G_i.
--
-- Here we don't use path as a sequence and save tree structure.
--
-- **This implementation doesn't use external predicates.**
--
data ChTree = ChNode ChStep
            | ChBranch ChStep [ChTree]
            | ChRoot [ChTree]
  deriving (Show, Eq)

--chTreeToTerm :: ChTree -> G


-- TODO: totality? what is better?
getStep (ChNode s) = s
getStep (ChBranch s _) = s
getStep _ = error "Root has no step"
--getStep (ChRoot _) = (0, 0)

--
--msgChAtoms :: [ChAtom S] -> ChAtom S
-- So we could sort list of trees by the atop position.
--
-- We use sorting to match branches of two trees.
--
instance Ord ChTree where
  compare (ChRoot _) (ChRoot _) = EQ
  compare s1 s2
    | a1 <- fst $ getStep s1
    , a2 <- fst $ getStep s2
    = compare a1 a2

fromMaybeList = sequenceA . filter isJust

sldToChTree :: SldTreeInner -> ChTree
sldToChTree FFail = ChRoot []
sldToChTree (SSuccess _ atom) = ChNode (1, atom)
sldToChTree (OOr ct _) = maybe (ChRoot []) ChRoot $ fromMaybeList (uncurry sldToChTree' <$> ct)
 where
  sldToChTree' :: ClauseNum -> SldTreeInner -> Maybe ChTree
  sldToChTree' claus (SSuccess _ atom) = Just $ ChNode (atom, claus)
  sldToChTree' claus (CConj sld _ _ atom)
    = (\t -> case t of { [] -> ChNode (atom, claus); _ -> ChBranch (atom, claus) t}) <$> nextTrees sld
  sldToChTree' _ _ = Nothing

  nextTrees (OOr ct _) = let a = fromMaybeList $ uncurry sldToChTree' <$> ct
    in case null <$> a of {Just True -> Nothing; _ -> a}
  nextTrees FFail      = Nothing
  nextTrees _          = Just []
sldToChTree (CConj _ _ _ _) =
  error "Why the root of the SldTree is a conjunction?"
sldToChTree (LLeaf _ _ _) = error "Can be LLeaf without a Conj?"

--
-- P -- program, U - unfolding rule.
--
-- chtree(<- Q, P, U) = t, t -- characteristic tree
--
-- Assume P and U is given.
--chTreeOp :: G X -> (ChTree, G S)
--chTreeOp = (sldToChTree A.&&& id) . topLevel'
chTreeOp :: G X -> ChTree
chTreeOp = sldToChTree . topLevel'

--
-- Abstraction operator.
--
-- Let P be a normal program,
--     U an unfolding rule and
--     A a set of atoms.
-- For every characteristic tree t, let A_t be defined as
-- A_t = { A' | A' in A and chtree(<- A', P, U) = t }.
--
-- The abstraction operator defined as
--  chabs_{P, U}(A) = { msg(A_t) | t is characteristic tree }
--
--  Assume we aleady work over given P and U.
--
--  Use the most inefficient solution we could possibly imagine.
chTreeAbsOp :: E.Delta -> [(Atom S, E.Gamma)] -> [Atom S]
chTreeAbsOp dlt goals = let
  xs = sortOn fst $ A.first (sldToChTree . uncurry sldRes) <$> zip goals (fst <$> goals)
  -- For debug save chTree
  --groupedByChTree = (A.first head . unzip) <$> groupBy (\a b -> fst a == fst b) xs
  groupedByChTree = (snd . unzip) <$> groupBy (eqBy fst) xs
  --in groupedByChTree
  --in foldr (\l (dlt, acc) -> (\a dlt' -> (dlt', a:acc)) $ msgAtom dlt l) (dlt, []) groupedByChTree
  in (fst . msgAtom dlt) <$> groupedByChTree
  where sldRes goal gamma = sldResolutionAtom goal gamma E.s0

--
-- We use ChAtom for preserving a ChTree and a Goal,
-- but we don't use the semanic of ChAtom (aka ecological partial deduction).
--
--chTreeAbsOp' :: [ChAtom S] -> [[G S]]
--chTreeAbsOp' = fmap (minimallyGeneral . fmap chAtom)
--             . groupBy (eqBy chTree)
--             . sortOn chTree
--

eqBy f = curry (uncurry (==) . (f A.*** f))

--
-- Find common subtreee with the same root.
--
genChTree :: ChTree -> ChTree -> Maybe ChTree
genChTree (ChRoot t1) (ChRoot t2) =
  let zipped = zip (sort t1) (sort t2)
  in ChRoot <$> sequenceA (uncurry genChTree' <$> zipped)
  where
    genChTree' :: ChTree -> ChTree -> Maybe ChTree
    -- t1 and t2 could be branches as well.
    genChTree' n@(ChNode s1) t2
      | s1 == (getStep t2) = Just n
    genChTree' t1 n@(ChNode s2)
      | (getStep t1) == s2 = Just n
    -- I suppose we dont' care if one of the branches doesn't match.
    genChTree' (ChBranch s1 t1) (ChBranch s2 t2)
      | s1 == s2 =
        let zipped = zipBy (fst . getStep) t1 t2
        in ChBranch s1 <$> fromMaybeList (uncurry genChTree' <$> zipped)
    genChTree' _ _ = Nothing

--
-- Check if tree t2 is more general t1.
--
moreGeneralTree :: ChTree -> ChTree -> Bool
moreGeneralTree (ChRoot t1) (ChRoot t2)
  | length t1 == length t2
  = all (uncurry moreGeneralTree) $  zip t1 t2
moreGeneralTree (ChNode s1) t2 = s1 == (getStep t2)
moreGeneralTree (ChBranch s1 ch1) (ChBranch s2 ch2)
  | s1 == s2
  = all (uncurry moreGeneralTree) $ zipBy getStep ch1 ch2
moreGeneralTree _ _ = False

--- *msg* for chtrees.
msgChTrees :: [ChTree] -> ChTree
msgChTrees [] = ChRoot []
msgChTrees (x:xs) = foldr msgChTrees2 x xs

msgChTrees2 :: ChTree -> ChTree -> ChTree
msgChTrees2 t = fromMaybe (ChRoot []) . msgChTrees' t

msgChTrees' :: ChTree -> ChTree -> Maybe ChTree
msgChTrees' (ChRoot t1) (ChRoot t2)
  | length t1 == length t2
  = ChRoot <$> sequenceA ((uncurry msgChTrees') <$> zip (sort t1) (sort t2))
  | otherwise = Nothing
msgChTrees' (ChBranch s1 t1) (ChBranch s2 t2)
  | s1 == s2
  , length t1 == length t2
  , Just t <- sequenceA ((uncurry msgChTrees') <$> zip (sort t1) (sort t2))
  = Just $ ChBranch s1 t
  | s1 == s2
  = Just $ ChNode s1
msgChTrees' (ChNode s1) (ChNode s2)
  | s1 == s2
  = Just $ ChNode s1
msgChTrees' (ChNode s1) (ChBranch s2 _)
  | s1 == s2
  = Just $ ChNode s1
msgChTrees' (ChBranch s1 _) (ChNode s2)
  | s1 == s2
  = Just $ ChNode s1
msgChTrees' _ _ = Just $ ChRoot []

--
-- Check if chtree b is instance of chtree a.
--
-- But there's no definition for chtrees.
--
-- So we take  *more general* definition.
--
instTree :: ChTree -> ChTree -> Bool
instTree a b = a == b || moreGeneralTree a b

--
-- Characteristic atom is a couple (A, t)
-- consiting of an atom A and its characteristic tree.
--
data ChAtom a = ChAtom { chAtom :: Atom a, chTree :: ChTree }
  deriving (Eq, Ord, Show)

isSubst (ChAtom [] _) = True
isSubst _ = False

isEmpty (ChAtom _ (ChRoot [])) = True
isEmpty _ = False

atomToChAtom :: E.Gamma -> E.Sigma -> Atom S -> ChAtom S
atomToChAtom env subst goal = ChAtom goal (sldToChTree $ sldResolutionAtom goal env subst)

--
-- By definition (Controlling Generalization and Polyvariance, p. 25, def. 4.3.15)
-- Let (A_1, t_1) and (A_2, t_2) be two chatoms such that msg is defined.
-- Then msg((A_1, t_2), (A_2, t_2)) = (msg(A_1, A_2), msg(t_1, t_2))
msgChAtoms :: E.Delta -> [ChAtom S] -> (ChAtom S, E.Delta)
msgChAtoms dlt chatoms = let (atom, dlt') = msgAtom dlt $ chAtom <$> chatoms
  in (ChAtom atom (msgChTrees $ chTree <$> chatoms), dlt')

instance AlwaysEmbeddable (ChAtom a) where
  -- TODO: how to use trees?
  isAlwaysEmbeddable = isAlwaysEmbeddable . chAtom

instance (Eq a, Ord a) => Instance a (ChAtom a) where
  inst :: ChAtom a -- a1
       -> ChAtom a -- a2, a2 is instance of a1 by substitution.
       -> Map.Map a (Term a) -- Substitution accumulator
       -> Maybe (Map.Map a (Term a)) 
  inst cha1 cha2 subst
    | instTree (chTree cha1) (chTree cha2) = inst (chAtom cha1) (chAtom cha2) subst
    | otherwise = Nothing

instance (Eq a, Ord a, Show a) => Embed a (ChAtom a) where
  embed :: ChAtom a -> ChAtom a -> Bool
  embed at1@(ChAtom a1 ch1) at2@(ChAtom a2 ch2) =
    homeo at1 at2 && not (isStrictInst at1 at2)

-- Homeomorphic embedding.
-- (A1, t1) <| (A2, t2) iff A1 <| A2 && t1 <| t2
instance Show a => Homeo (ChAtom a) where
  couple (ChAtom atom1 chtree1) (ChAtom atom2 chtree2)
    = couple atom1 atom2 && coupleTree chtree1 chtree2
  diving (ChAtom atom1 chtree1) (ChAtom atom2 chtree2)
    = diving atom1 atom2 && divingTree chtree1 chtree2
  homeo (ChAtom atom1 chtree1) (ChAtom atom2 chtree2)
    = homeo atom1 atom2 && homeoTree chtree1 chtree2

coupleTree :: ChTree -> ChTree -> Bool
coupleTree (ChRoot ch1) (ChRoot ch2)
  | length ch1 == length ch2 = all (uncurry homeoTree) $ zip ch1 ch2
coupleTree (ChBranch s1 ch1) (ChBranch s2 ch2)
  | s1 == s2
  , length ch1 == length ch2 = all (uncurry homeoTree) $ zip ch1 ch2
coupleTree (ChNode s1) (ChNode s2) = s1 == s2
coupleTree _ _ = False

divingTree :: ChTree -> ChTree -> Bool
divingTree (ChRoot ch1) (ChRoot ch2)
  | length ch1 < length ch2 = any (all (uncurry homeoTree) . zip ch1) $ subconjs ch2 (length ch1)
divingTree ch1@(ChBranch s1 _) (ChBranch s2 ch2)
  | s1 /= s2 = any (homeoTree ch1) ch2
divingTree ch1@(ChNode s1) (ChBranch s2 ch2)
  | s1 == s2 = True
  | otherwise = any (homeoTree ch1) ch2
divingTree _ _ = False

homeoTree x y = coupleTree x y || divingTree x y

sldResolutionAtom :: Atom S -> E.Gamma -> E.Sigma -> SldTreeInner
sldResolutionAtom goal gamma subst = sldResolutionStep'
  ((flip Descend Set.empty) <$> goal)
  gamma
  subst
  Set.empty
  True

atomPos = succ . length

sldResolutionStep'
  :: [DescendGoal] -> E.Gamma -> E.Sigma -> Set.Set [G S] -> Bool -> SldTreeInner
sldResolutionStep' gs env@(p, i, d@(temp : _)) s seen isFirstTime
  | variantCheck (map getCurr gs) seen
  = LLeaf gs s env
  | Just (ls, Descend g ancs, rs) <- selectNext gs
  = let (g', env') = unfold g env
    in go g' env' ls rs g ancs isFirstTime
  | otherwise
  = LLeaf gs s env
 where
  go g' env' ls rs g ancs isFirstTime
    = let
        normalized = normalize g'
        unified    = fmap fromJust <$> filter (isJust . snd)
          (A.second (unifyStuff s) <$> zip [1 ..] normalized)
      in
        -- trace ("\nGoal: " ++ show g' ++ "\n"
        --   ++ "Normalized (" ++ show (length normalized) ++ "): " ++ show normalized ++ "\n"
        --   ++ "Unified (" ++ show (length unified) ++ "): " ++ show unified ++ "\n" )$
        case snd <$> unified of
          [] -> FFail
          ns | length ns == 1 || isFirstTime ->
           let cond = isFirstTime && length ns == 1
           in OOr (fmap (step cond) <$> unified) s
          ns | not (null rs) -> maybe
            (LLeaf gs s env)
            (\(ls', Descend nextAtom nextAtomsAncs, rs') ->
              let (g'', env'') = unfold nextAtom env
                  ls'' = ls ++ (Descend g ancs : ls')
              in go g'' env'' ls'' rs' nextAtom nextAtomsAncs False
            )
            (selectNext rs)
          ns -> LLeaf gs s env
    where
      insertDescendAncs = fmap (\x -> Descend x (Set.insert g ancs))
      addDescends xs s = substituteDescend s (ls ++ insertDescendAncs xs ++ rs)

      step cond (xs, s')
        | null xs && null rs
        = SSuccess s' (atomPos ls)
        | otherwise
        = let newDescends = addDescends xs s'
              newSeen     = Set.insert (map getCurr gs) seen
              tree = sldResolutionStep' newDescends env' s' newSeen cond
          in  CConj tree newDescends s' (atomPos ls)


type Goal = G X
type LogicGoal = (G S, E.Gamma, E.Delta)

goalToLogicGoal :: Goal -> LogicGoal
goalToLogicGoal goal = let
  (goal', _, defs)       = justTakeOutLets (goal, [])
  gamma                  = E.updateDefsInGamma E.env0 defs
  in E.preEval' gamma goal'

topLevel' :: Goal -> SldTreeInner
topLevel' goal =
  let (logicGoal, gamma, _) = goalToLogicGoal goal
  in  sldResolutionStep' [Descend logicGoal Set.empty]
                         gamma
                         E.s0
                         Set.empty
                         True

data Resultant = Resultant {
    resSubst :: E.Sigma
  , resAtom :: Atom S
  , resGamma :: E.Gamma
  }

instance Show Resultant where
  show (Resultant s a g) = "Resultant {" ++ show s ++ ", " ++ show a ++ "}"

-- Interface.
resultant :: E.Sigma -> Atom S -> E.Gamma -> Resultant
resultant = Resultant

isResultantSubst = null . resAtom

showResultants (_, gls, _) = "{" ++ show gls ++ "}"
showResult rs = "[" ++ concat ((\(r, cp) -> showResultants r ++ ", " ++ show cp ++ "\n") <$> rs) ++ "]"

-- TODO: need to return sldtree?
-- TODO: what if atom is empty?
resultantToChAtom (Resultant subst atom env) = let
    sldtree = sldResolutionAtom atom env subst
    chtree  = sldToChTree sldtree
  in (ChAtom atom chtree, subst, env)


resultantsInner :: SldTreeInner -> [(Resultant, ChPath)]
resultantsInner = resultantsInner' [] 0

--
-- We ignore the second argument in `LLeaf`, `OOr` and `FFail` ctrs.
-- We assume that after `CConj` ctr `OOr` follows, so as ClauseNum we give 0
-- to show that we don't care (maybe need to do smth else, but whatever).
--
resultantsInner' :: ChPath -> ClauseNum -> SldTreeInner -> [(Resultant, ChPath)]
resultantsInner' path cls (SSuccess s ap)   = [(resultant s [] E.env0,
                                              reverse ((ap, cls):path))]
resultantsInner' path _ (LLeaf ds s env)    = [(resultant s (getCurr <$> ds) env, reverse path)]
resultantsInner' path cls (CConj ch _ _ ap) = resultantsInner' ((ap, cls):path) 0 ch
resultantsInner' path _   (OOr disjs _)     = concatMap (uncurry (resultantsInner' path)) disjs
resultantsInner' _ _ FFail                  = []
