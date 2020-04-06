{-# LANGUAGE ScopedTypeVariables #-}

module SC.SC where
    
import SC.DTree
import Syntax
import Embedding

import qualified Eval as E
-- import qualified Driving as D
import qualified Purification as P
import qualified Generalization as G

import Utils
import DotPrinter

import Data.Maybe (mapMaybe)
import Data.List (group, sort, groupBy, find, intersect, delete, sortBy)
import qualified Data.Set as Set
import Data.Tuple (swap)

import Text.Printf
import Debug.Trace

import Control.Arrow (first)
import Control.Exception
import PrettyPrint

trace' _ = id
-- trace' = trace

class Show a => UnfoldableGoal a where
  -- Что-то вроде интерфейса для `a'. Может, следует вынести в отдельный класс.
  -- Получить цель из `a'.
  getGoal    :: a -> DGoal
  -- Сконструировать `a'.
  initGoal   :: DGoal -> a
  -- Проверить, пустая ли конъюнкция.
  emptyGoal  :: a -> Bool
  -- Применить функцию к цели в `a'.
  mapGoal    :: a -> (DGoal -> DGoal) -> a
  --
  -- `unfold` цели в `a'.
  --
  unfoldStep :: a -> E.Gamma -> E.Sigma -> ([(E.Sigma, a)], E.Gamma)

type Derivable a =  a -> Set.Set DGoal -> E.Gamma -> E.Sigma -> Set.Set DGoal -> Int -> (DTree, Set.Set DGoal, S)

type SuperCompGen a = G X -> (DTree' a, G S, [S])

type SuperComp = SuperCompGen DGoal

newtype Derive a = Derive { derive :: Derivable a }

supercomp :: UnfoldableGoal a => Derive a -> SuperComp
supercomp d g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  lgoal' = normalize lgoal
  igoal = assert (length lgoal' == 1) $ initGoal (head lgoal')
  tree = fst3 $ derive d igoal Set.empty lgamma E.s0 Set.empty 1
  in (tree, lgoal, lnames)

fixEnv i (f1, f2, d:ds)
  | i > d = (f1, f2, drop (i - d) ds)
  | otherwise = (f1, f2, ds)

maxFreshVar = head . trd3

getVariant goal nodes = let
    vs = Set.filter (isVariant goal) nodes
  in assert (length vs == 1) $ Set.elemAt 0 vs

--

goalXtoGoalS :: G X -> (G S, E.Gamma, [S])
goalXtoGoalS g = let
  (goal, _, defs)    = P.justTakeOutLets (g, [])
  gamma              = E.updateDefsInGamma E.env0 defs
  in E.preEval' gamma goal

--

isGen goal ancs = any (`embed` goal) ancs && not (Set.null ancs)

isUpwardGen goal ancs = any (isUpwardGenP goal) ancs && not (Set.null ancs)
isUpwardGenP goal anc = embed goal anc && not (embed anc goal) && length goal == length anc

--

unfold :: G S -> E.Gamma -> (E.Gamma, G S)
unfold g@(Invoke f as) env@(p, i, d)
  | (n, fs, body) <- p f
  , length fs == length as
  = let i' = foldl extend i (zip fs as)
        (g', env', names) = E.preEval' (p, i', d) body
    in (env', g')
  | otherwise = error "Unfolding error: different number of factual and actual arguments"
unfold g env = (env, g)

extend :: E.Iota -> (X, Ts) -> E.Iota
extend = uncurry . E.extend

--

unifyAll :: E.Sigma -> Disj (Conj (G S)) -> Disj (Conj (G S), E.Sigma)
unifyAll = mapMaybe . unifyStuff

--
-- Conjunction of DNF to DNF
--
conjOfDNFtoDNF :: Ord a => Conj (Disj (Conj a)) -> Disj (Conj a)
conjOfDNFtoDNF [] = []
conjOfDNFtoDNF [x] = x
conjOfDNFtoDNF (x {- Disj (Conj a) -} :xs) = concat $ addConjToDNF x <$> conjOfDNFtoDNF xs {- Disj (Conj a) -}

addConjToDNF :: Disj (Conj a) -> Conj a -> Disj (Conj a)
addConjToDNF ds c = (c ++) <$> ds

-- |Check if a goal is a renaming (in terms of local programming) of already met goal.
checkLeaf :: DGoal -> Set.Set DGoal -> Bool
checkLeaf = variantCheck

-- |Check if we after abstraction we got a renaming.
abstractSame [(_, aGoal, _, _)] goal = isVariant aGoal goal
abstractSame _ _ = False


abstractU
  :: Set.Set [G S]               -- Ancestors of the goal
  -> [G S] -> E.Sigma -> E.Gamma -- Body: the goal with subst and ctx
  -> [(E.Sigma, [G S], G.Generalizer, E.Gamma)]
abstractU ancs g subst (p, iota, delt) =
  let (abstracted, delta) = abstractU' ancs g delt
  in  map (\(g, gen) -> (subst, g, gen, (p, iota, delta))) abstracted
  where
   abstractU'  ancs g delt
     | Just anc <- findAncUpward g ancs
     = generalize g anc delt
     | otherwise
     = error $ "Unable to generalize (U) <" ++ show g ++ "> with ancs: " ++ show ancs

abstract
  :: Set.Set [G S]               -- Ancestors of the goal
  -> [G S] -> E.Sigma -> E.Gamma -- Body: the goal with subst and ctx
  -> [(E.Sigma, [G S], G.Generalizer, E.Gamma)]
abstract = abstractChild

abstractChild
  :: Set.Set [G S]               -- Ancestors of the goal
  -> [G S] -> E.Sigma -> E.Gamma -- Body: the goal with subst and ctx
  -> [(E.Sigma, [G S], G.Generalizer, E.Gamma)]
abstractChild ancs g subst (p, iota, delt) =
  let (abstracted, delta) = abstract' ancs g delt
  in  map (\(g, gen) -> (subst, g, gen, (p, iota, delta))) abstracted

abstractFixed
  :: Set.Set [G S]               -- Ancestors of the goal
  -> [G S] -> E.Sigma -> E.Gamma -- Body: the goal with subst and ctx
  -> ([(E.Sigma, [G S], G.Generalizer)], E.Gamma)
abstractFixed ancs g subst (p, iota, delt) =
  let (abstracted, delta) = abstract' ancs g delt
  in  (map (\(g, gen) -> (subst, g, gen)) abstracted, (p, iota, delta))

abstractDebug ancs g subst delt =
  let (abstracted, delta) = abstract' ancs g delt
  in  map (\(g, gen) -> (subst, g, gen)) abstracted

abstract' ancs g delt
  | Just anc <- findAnc g ancs
  = generalize g anc delt
  | otherwise
  = error $ "Unable to generalize <" ++ pretty g ++ "> with ancs: " ++ prettyList (Set.toList ancs)

findAncUpward g = find (embed g) . sortBy goalOrdering . Set.toList
  where
    goalOrdering a1 a2 = compare (length a2) (length a1)

-- |Find a parent who is embeded in us.
findAnc g = find (`embed` g) . sortBy goalOrdering . Set.toList
  where
    goalOrdering a1 a2 = compare (length a2) (length a1)
    {-
    goalOrdering a1 a2
      | isVariant a1 a2 = EQ
      | a1 `embed` a2 = GT
      | otherwise = LT
    -}

findRenaming goal = find (isVariant goal)

-- Old whistles.

-- |Strict whisle using strict homeo embedding
whistleStrict :: Set.Set [G S] -> [G S] -> Maybe [G S]
whistleStrict ancs m = find (\b -> embed b m && not (isVariant b m)) ancs

-- |
whistle :: Set.Set [G S] -> [G S] -> Bool
whistle ancs goal = any (whistleP goal) ancs

whistleP goal anc = homeo anc goal  && not (isVariant anc goal)

findW goal = find (whistleP goal)

-- |Generalization at its core.

generalize :: [G S] -> [G S] -> E.Delta -> ([([G S], G.Generalizer)], E.Delta)
generalize = generalizeCpd

generalizeCpd :: [G S] -> [G S] -> E.Delta -> ([([G S], G.Generalizer)], E.Delta)
generalizeCpd m b d =
  let ((m1, m2), genOrig, delta) = G.split d b m in
  (map (,genOrig) (G.mcs m1) ++ map (,[]) (G.mcs m2), delta)

--generalizeCpd' :: [G S] -> [G S] -> E.Delta -> ([([G S], G.Generalizer)], E.Delta)
generalizeCpd' m b d =
  let ((m1, m2), genOrig, delta) = G.split d b m in
  -- ((map (,genOrig) (G.mcs m1)) ++ (map (,[]) (G.mcs m2)), delta)
  (m1, m2, genOrig)

{-
  TODO: describe generalization, add SPLIT step
-}
generalizeSimple :: [G S] -> [G S] -> E.Delta -> ([([G S], G.Generalizer)], E.Delta)
generalizeSimple goal anc delt = 
  let (g, _, gen, delt') = G.generalizeGoals delt goal anc
  in ([(g, gen)], delt')

-- |Check if we need to do a split step.
toSplit :: [G S] -> Bool
toSplit = null . foldl1 intersect . map getInvokeArgs . filter isInvoke

--
getInvokeArgs (Invoke _ ts) = ts
getInvokeArgs _ = []

--
isInvoke (Invoke _ _) = True
isInvoke _ = False

--
getInvokeName (Invoke name _) = name
getInvokeName g = error $ "getInvokeName: not Invoke: " ++ show g

-- |Goal normaliztion.
normalize :: G a -> [[G a]]
normalize (f :\/: g) = normalize f ++ normalize g
normalize (f :/\: g) = (++) <$> normalize f <*> normalize g
normalize g@(Invoke _ _) = [[g]]
normalize g@(_ :=: _) = [[g]]
normalize (Fresh _ goal) = normalize goal

-- |To avoid code repeatition and exhausting renaming.
goalToDNF = normalize

-- |Apply unifications and add some more of them.
unifyStuff :: E.Sigma -> [G S] -> Maybe ([G S], E.Sigma)
unifyStuff state gs = go gs state [] where
  go []                    state conjs = Just (reverse conjs, state)
  go (g@(Invoke _ _) : gs) state conjs = go gs state (g : conjs)
  go ((t :=: u) : gs)      state conjs = do
    s <- E.unify  (Just state) t u
    go gs s conjs

genUnfoldStep :: UnfoldableGoal a =>
     (E.Gamma -> a -> (DGoal, G S, DGoal))
  -> (DGoal -> a)
  -> a
  -> E.Gamma
  -> E.Sigma
  -> ([(E.Sigma, a)], E.Gamma)
genUnfoldStep split ctr goal env subst = let
    (ls, conj, rs) = split env goal
    (newEnv, uConj) = unfold conj env

    nConj = goalToDNF uConj
    unConj = unifyAll subst nConj
    us = (\(cs, subst) -> (subst, construct subst cs ls rs)) <$> unConj
  in (us, newEnv)
  where
    construct subst cs ls rs = ctr $ E.substitute subst $ ls ++ cs ++ rs

class UnfoldableGoal a => Unfold a where
  derivationStep
    :: a                 -- Conjunction of invokes and substs.
    -> Set.Set DGoal     -- Ancsectors.
    -> E.Gamma           -- Context.
    -> E.Sigma           -- Substitution.
    -> Set.Set DGoal     -- Already seen.
    -> Int -- depth for debug
    -> (DTree, Set.Set DGoal, S)
  derivationStep = undefined
