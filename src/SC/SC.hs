{-# LANGUAGE ScopedTypeVariables #-}

module SC.SC where
    
import SC.DTree
import Syntax
import Embedding

import qualified CPD.LocalControl as CPD
import qualified Eval as E
-- import qualified Driving as D
import qualified Purification as P
import qualified Generalization as D

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


class UnfoldableGoal a => Unfold a where
  --
  -- `unfold` цели в `a'.
  --
  unfoldStep :: a -> E.Gamma -> E.Sigma -> ([(E.Sigma, a)], E.Gamma)


  derivationStep
    :: a                 -- Conjunction of invokes and substs.
    -> Set.Set DGoal     -- Ancsectors.
    -> E.Gamma           -- Context.
    -> E.Sigma           -- Substitution.
    -> Set.Set DGoal     -- Already seen.
    -> Int -- depth for debug
    -> (DTree, Set.Set DGoal, S)
  derivationStep goal ancs env subst seen depth
    -- | depth >= 5
    -- = (Prune (getGoal goal), seen, maxFreshVar env)
    | checkLeaf (getGoal goal) seen
    = (Leaf (CPD.Descend (getGoal goal) ancs) subst env, seen, maxFreshVar env)
    | otherwise
    =
    let
      realGoal = getGoal goal
      descend = CPD.Descend realGoal ancs
      newAncs = Set.insert realGoal ancs
      -- Add `goal` to a seen set (`Or` node in the tree).
    in case unfoldStep goal env subst of
       ([], _)          -> (Fail, seen, maxFreshVar env)
       (uGoals, newEnv) -> let
           -- Делаем свёртку, чтобы просмотренные вершины из одного обработанного поддерева
           -- можно было передать в ещё не обработанное.
           newSeen = Set.insert realGoal seen
           (seen', ts, maxVarNum) = foldl (\(seen, ts, m) g ->
               (\(a, t, i) -> (a, t:ts, max i m)) $
                 evalSubTree depth (fixEnv m newEnv) newAncs seen g)
               (newSeen, [], maxFreshVar env) uGoals
         in (Or (reverse ts) subst descend, seen', maxVarNum)

  evalSubTree :: Int -> E.Gamma -> Set.Set DGoal -> Set.Set DGoal -> (E.Sigma, a) -> (Set.Set DGoal, DTree, S)
  evalSubTree depth env ancs seen (subst, goal)
    | emptyGoal goal
    = (seen, Success subst, maxFreshVar env)
    | not (checkLeaf realGoal seen)
    , isGen realGoal ancs
    =
      let
        absGoals = abstract ancs realGoal subst env
     -- in
     --  trace ("Goal: " ++ pretty realGoal
     --         ++ "\nAncs: " ++ show ancs ++ "\n"
     --         ++ show (length absGoals)
     --         ++ "\nAbs:  " ++ show ((\(_,g,_,_) -> pretty g ++ " <|> ") <$> absGoals) ++ "\n"
     --         ) $
     -- let

        -- Add `realGoal` to a seen set (`And` node in the tree).
        newSeen = Set.insert realGoal seen

        (seen', ts, maxVarNum) = foldl (\(seen, ts, m) g ->
                (\(a, t, i) -> (a, t:ts, max i m)) $
                evalGenSubTree m depth ancs seen g)
                (newSeen, [], maxFreshVar env) absGoals
      in (seen', And (reverse ts) subst descend, maxVarNum)
    | otherwise
    =
      let
        (tree, seen', maxVarNum) = derivationStep goal ancs env subst seen (succ depth)
      in (seen', tree, maxVarNum)
    where
      realGoal = getGoal goal
      descend  = CPD.Descend realGoal ancs

      evalGenSubTree m depth ancs seen (subst, goal, gen, env') =
        let
          env = fixEnv m env'
          (tree, seen', maxVarNum) = derivationStep ((initGoal :: DGoal -> a) goal) ancs env subst seen (succ depth)
          subtree  = if null gen then tree else Gen tree gen
        in (seen', subtree, maxVarNum)

{-
  derivationStep = derivationStep' False

  derivationStep'
    :: Bool -> a                 -- Conjunction of invokes and substs.
    -> Set.Set DGoal     -- Ancsectors.
    -> E.Gamma           -- Context.
    -> E.Sigma           -- Substitution.
    -> Set.Set DGoal     -- Already seen.
    -> Int -- depth for debug
    -> (DTree, Set.Set DGoal, S)
  derivationStep' skip goal ancs env subst seen d
    | d > 6
    = (Prune (getGoal goal), seen, 0)
    -- Empty goal => everything evaluated fine
    | emptyGoal goal
    = (Success subst, seen, maxFreshVar env)
    -- If we already seen the same node, stop evaluate it.
    | checkLeaf (getGoal goal) seen
    = (Leaf (CPD.Descend (getGoal goal) ancs) subst env, seen, maxFreshVar env)
    -- If a node is generalization of one of ancsectors generalize.
    | not skip
    , isGen (getGoal goal) ancs
    = let
        rGoal = getGoal goal
        aGoals = abstract ancs rGoal subst env
      -- in trace ("Goal: " ++ pretty rGoal
      --         ++ "\nAbs:  " ++ show ((\(_,g,_,_) -> pretty g) <$> aGoals) ++ "\n"
      --         ++ "Ancs: " ++ show ancs ++ "\n"
      --         ) $
      -- let
        nAncs = Set.insert rGoal ancs
        nSeen = Set.insert rGoal seen
        (seen', trees, maxVarNum) =
          foldl
            (\(seen, ts, m) (subst, goal, gen, nEnv) ->
              let (t, seen'', mv) = derivationStep' (isVariant goal rGoal) ((initGoal :: DGoal -> a) goal) nAncs (fixEnv m nEnv) subst seen (succ d)
                  t' = if null gen then t else Gen t gen
              in (seen'', t':ts, mv)
            )
            (nSeen, [], maxFreshVar env)
            aGoals
        tree = And trees subst (CPD.Descend rGoal ancs)
      in (tree, seen', maxVarNum)
    | otherwise
    = case unfoldStep goal env subst of
        ([], _) -> (Fail, seen, maxFreshVar env)
        (uGoals, nEnv) -> let
            rGoal = getGoal goal
            nAncs = Set.insert rGoal ancs
            nSeen = Set.insert rGoal seen

            (seen', trees, maxVarNum) =
              foldl
                (\(seen, ts, m) (subst, goal) ->
                  let (t, seen'', mv) = derivationStep' False goal nAncs (fixEnv m nEnv) subst seen (succ d)
                  in (seen'', t:ts, mv)
                )
                (nSeen, [], maxFreshVar nEnv)
                uGoals

            tree = Or (reverse trees) subst (CPD.Descend rGoal ancs)
          in (tree, seen', maxVarNum)
-}


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
unifyAll = mapMaybe . CPD.unifyStuff

--
-- Conjunction of DNF to DNF
--
conjOfDNFtoDNF :: Ord a => Conj (Disj (Conj a)) -> Disj (Conj a)
conjOfDNFtoDNF [] = []
conjOfDNFtoDNF (x:[]) = x
conjOfDNFtoDNF (x {- Disj (Conj a) -} :xs) = concat $ addConjToDNF x <$> conjOfDNFtoDNF xs {- Disj (Conj a) -}

addConjToDNF :: Disj (Conj a) -> Conj a -> Disj (Conj a)
addConjToDNF ds c = (c ++) <$> ds

checkLeaf = variantCheck
-- Fair renaming
{-
checkLeaf' g = any (\sg -> all' $ uncurry isRenaming <$> zip' g sg)
  where
    all' [] = False
    all' xs = all id xs

    zip' xs ys
      | length xs == length ys
      = zip xs ys
      | otherwise
      = []
-}

abstract
  :: Set.Set [G S]                         -- Ancestors of the goal
  -> [G S] -> E.Sigma -> E.Gamma -- Body: the goal with subst and ctx
  -> [(E.Sigma, [G S], D.Generalizer, E.Gamma)]
abstract = abstractChild

abstractChild
  :: Set.Set [G S]                         -- Ancestors of the goal
  -> [G S] -> E.Sigma -> E.Gamma -- Body: the goal with subst and ctx
  -> [(E.Sigma, [G S], D.Generalizer, E.Gamma)]
abstractChild ancs g subst (p, iota, delt) =
  let (abstracted, delta) = abstract' ancs g delt
  in  map (\(g, gen) -> (subst, g, gen, (p, iota, delta))) abstracted

abstract' ancs g delt
  | Just anc <- find (`embed` g) $ sortAncs $ Set.toList ancs
  =
   let r = generalize g anc delt
   in
    --trace ("Generalize " ++ pretty g ++ "\nwith anc: " ++ pretty anc
    --  ++ "\nposs: " ++ prettyList (delete anc $ filter (`embed` g) $ Set.toList ancs)
    --  ++ "\nAnd got: " ++ show (fst r) ++ "\n") $
    r
  | otherwise
  = error $ "Unable to generalize <" ++ pretty g ++ "> with ancs: " ++ prettyList (Set.toList ancs)

sortAncs = sortBy goalOrdering

goalOrdering a1 a2
  | isVariant a1 a2 = EQ
  | a1 `embed` a2 = GT
  | otherwise = LT

{-
abstract'
  :: Set.Set [G S] -- The goal's ancs
  -> [G S]         -- The goal
  -> E.Delta       -- Set of used semantic variables
  -> ([([G S], D.Generalizer)], E.Delta)
abstract' ancs goals d =
  let qCurly = CPD.mcs goals in
  let result = go (map (, []) qCurly) d in
  result
   where
    go [] d@(x:_) = ([], d)
    go ((m, gen):gs) d =
      case whistle ancs m of
        Nothing ->
          let (goals, delta) = go gs d in
          ((m, gen) : goals, delta)
        Just b ->
          let (goals, delta) = generalize m b d in
          let (blah, halb) = go gs delta in
          (goals ++ blah, halb)
-}

whistle :: Set.Set [G S] -> [G S] -> Maybe [G S]
whistle ancs m = find (\b -> embed b m && not (isVariant b m)) ancs

generalize :: [G S] -> [G S] -> E.Delta -> ([([G S], D.Generalizer)], E.Delta)
generalize m b d =
  let ((m1, m2), genOrig, delta) = CPD.split d b m in
  ((map (,genOrig) (CPD.mcs m1)) ++ (map (,[]) (CPD.mcs m2)), delta)

toSplit :: [G S] -> Bool
toSplit = null . foldl1 intersect . map getInvokeArgs . filter isInvoke

getInvokeArgs (Invoke _ ts) = ts
getInvokeArgs _ = []

isInvoke (Invoke _ _) = True
isInvoke _ = False

getInvokeName (Invoke name _) = name
getInvokeName g = error $ "getInvokeName: not Invoke: " ++ show g

normalize :: G a -> [[G a]]
normalize (f :\/: g) = normalize f ++ normalize g
normalize (f :/\: g) = (++) <$> normalize f <*> normalize g
normalize g@(Invoke _ _) = [[g]]
normalize g@(_ :=: _) = [[g]]
normalize (Fresh _ goal) = normalize goal

genUnfoldStep :: UnfoldableGoal a =>
     (E.Gamma -> a -> (G S, DGoal))
  -> (DGoal -> a)
  -> a
  -> E.Gamma
  -> E.Sigma
  -> ([(E.Sigma, a)], E.Gamma)
genUnfoldStep split ctr goal env subst = let
    (conj, rest) = split env goal
    (newEnv, uConj) = unfold conj env

    nConj = goalToDNF uConj
    unConj = unifyAll subst nConj
    us = (\(cs, subst) -> (subst, construct subst cs rest)) <$> unConj
  in (us, newEnv)
  where
    construct subst cs rest = ctr $ E.substituteConjs subst $ cs ++ rest
