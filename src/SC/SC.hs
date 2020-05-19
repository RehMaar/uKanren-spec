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
import Data.List (group, sort, groupBy, find, intersect, delete, sortBy, intercalate)
import qualified Data.Set as Set
import Data.Tuple (swap)
import Data.Foldable (foldl')

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
  unfoldStep :: a -> E.Env -> E.Subst -> E.ConstrStore -> ([(E.Subst, E.ConstrStore, a)], E.Env)

type Derivable a = a -> [DGoal] -> E.Env -> E.Subst -> E.ConstrStore -> Set.Set DGoal -> Int -> (DTree, Set.Set DGoal, S)

type SuperCompGen a = G X -> (DTree' a, G S, [S])

type SuperComp = SuperCompGen DGoal

newtype Derive a = Derive { derive :: Derivable a }

supercomp :: UnfoldableGoal a => Derive a -> SuperComp
supercomp d g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  lgoal' = normalize lgoal
  igoal = assert (length lgoal' == 1) $ initGoal (head lgoal')
  tree = fst3 $ derive d igoal [] lgamma E.s0 [] Set.empty 1
  in (tree, lgoal, lnames)

fixEnv i (E.Env f1 f2 (d:ds))
  | i > d = E.Env f1  f2 $ drop (i - d + 1) ds
  | otherwise = E.Env f1 f2 ds

maxFreshVar = head . E.envNS

getVariant goal nodes = let
    vs = Set.filter (isVariant goal) nodes
  in assert (length vs == 1) $ Set.elemAt 0 vs

--
goalXtoGoalS :: G X -> (G S, E.Env, [S])
goalXtoGoalS g = let
  (goal, _, defs)    = P.justTakeOutLets (g, [])
  gamma              = E.updateDefsInGamma E.env0 defs
  in E.preEval' gamma goal
--

--
isGen goal ancs = any (`embed` goal) ancs && not (Set.null ancs)
--

unfold :: G S -> E.Env -> (E.Env, G S)
unfold g@(Invoke f as) env
  | (n, fs, body) <- E.envLookupDef env f
  , length fs == length as
  = let i' = foldl' extend (E.envIota env) (zip fs as)
        (g', env', names) = E.preEval' env{E.envIota = i'}  body
    in (env', g')
  | otherwise = error $ "Unfolding error: different number of factual and actual arguments of " ++ pretty g
unfold g env = (env, g)

extend :: E.Iota -> (X, Ts) -> E.Iota
extend = uncurry . E.extend

--

unifyAll :: E.Subst -> E.ConstrStore -> Disj (Conj (G S)) -> Disj (Conj (G S), E.Subst, E.ConstrStore)
unifyAll subst cstore = mapMaybe (unifyGoal subst cstore)

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
abstractSame [(aGoal, _)] goal = isVariant aGoal goal
abstractSame _ _ = False


abstract
  :: Set.Set [G S]
  -> [G S]
  -> E.Subst
  -> E.NameSupply
  -> [(E.Subst, [G S], G.Generalizer, E.NameSupply)]
abstract ancs g subst ns  =
  let (abstracted, delta) = abstract' ancs g ns
  in  map (\(g, gen) -> (subst, g, gen, delta)) abstracted

abstractFixed
  :: Set.Set [G S]
  -> [G S] -> E.Subst -> E.NameSupply
  -> ([(E.Subst, [G S], G.Generalizer)], E.NameSupply)
abstractFixed ancs g subst ns =
  let (abstracted, delta) = abstract' ancs g ns
  in  (map (\(g, gen) -> (subst, g, gen)) abstracted, delta)

abstractDebug ancs g subst delt =
  let (abstracted, delta) = abstract' ancs g delt
  in  map (\(g, gen) -> (subst, g, gen)) abstracted

abstract' ancs g delt
  | Just anc <- findAnc g ancs
  = -- trace ("Goal: " ++ show g ++ "\nAnc: " ++ show anc ++ "\n\n") $
    generalize g anc delt
  | otherwise
  = error $ "Unable to generalize <" ++ pretty g ++ "> with ancs: " ++ prettyList (Set.toList ancs)

abstractL
  :: [[G S]]
  -> [G S]
  -> E.NameSupply
  -> ([([G S], G.Generalizer)], E.NameSupply)
abstractL ancs g ns
  | Just anc <- findAnc' g ancs
  = generalize g anc ns
  | otherwise
  = error $ "Unable to generalize <" ++ pretty g ++ "> with ancs: " ++ prettyList ancs
  where findAnc' g = find (`embed` g) 

abstractS
  :: Set.Set [G S]
  -> [G S]
  -> E.NameSupply
  -> ([([G S], G.Generalizer)], E.NameSupply)
abstractS ancs g ns
  | Just anc <- findAnc g ancs
  = generalize g anc ns
  | otherwise
  = error $ "Unable to generalize <" ++ pretty g ++ "> with ancs: " ++ prettyList (Set.toList ancs)
  where findAnc' g = find (`embed` g) . reverse

-- |Find a goal for upward abstraction.
findAncUpward g = find (embed g) . sortBy goalOrdering . Set.toList
  where
    goalOrdering a1 a2 = compare (length a2) (length a1)

-- |Find a parent who is embeded in us.
findAnc g = find (`embed` g) . sortBy goalOrdering . Set.toList
  where
    goalOrdering a1 a2 = compare (length a1) (length a2)
    
findRenaming goal = find (isVariant goal)

-- Old whistles.

-- |Strict whisle using strict homeo embedding
whistleStrict :: Set.Set [G S] -> [G S] -> Maybe [G S]
whistleStrict ancs m = find (\b -> embed b m && not (isVariant b m)) ancs

-- |
whistle :: Set.Set [G S] -> [G S] -> Bool
whistle ancs goal = any (whistleP goal) ancs && not (Set.null ancs)

whistleP goal anc = embed anc goal  && not (isVariant anc goal)

whistleP' goal anc = homeo anc goal  && not (isVariant anc goal)

-- |Generalization at its core.
generalize ::
     [G S] -- |Goal
  -> [G S] -- |Parent
  -> E.NameSupply
  -> ([([G S], G.Generalizer)], E.NameSupply)
generalize = generalizeCpd

generalizeCpd :: [G S] -> [G S] -> E.NameSupply -> ([([G S], G.Generalizer)], E.NameSupply)
generalizeCpd m b d =
  let ((m1, m2), genOrig, delta) = G.split d b m in
  (map (,genOrig) (G.mcs m1) ++ map (,[]) (G.mcs m2), delta)

{-
  TODO: describe generalization, add SPLIT step
-}
generalizeSimple :: [G S] -> [G S] -> E.NameSupply -> ([([G S], G.Generalizer)], E.NameSupply)
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
normalize (Fresh _ goal) = normalize goal
normalize g = [[g]]

-- |To avoid code repeatition and exhausting refactor renaming.
goalToDNF = normalize

-- |Apply unifications and add some more of them.
unifyStuff :: E.Subst -> [G S] -> Maybe ([G S], E.Subst)
unifyStuff state gs = go gs state [] where
  go []                    state conjs = Just (reverse conjs, state)
  go (g@(Invoke _ _) : gs) state conjs = go gs state (g : conjs)
  go ((t :=: u) : gs)      state conjs = do
    s <- E.unify  (Just state) t u
    go gs s conjs


-- |Generalized unfold step.
-- <split> function defines the way to split a goal into a node to
-- actualy unfold and the rest of the goal..
genUnfoldStep :: UnfoldableGoal a =>
     (E.Env -> a -> (DGoal, G S, DGoal))
  -> (DGoal -> a)
  -> a
  -> E.Env
  -> E.Subst
  -> E.ConstrStore
  -> ([(E.Subst, E.ConstrStore, a)], E.Env)
genUnfoldStep split ctr goal env subst cstore = let
    (ls, conj, rs) = split env goal
    (newEnv, uConj) = unfold conj env

    nConj = goalToDNF uConj
    unConj = unifyAll subst cstore nConj
    us = (\(cs, subst, cstore) -> (subst, cstore, construct subst cs ls rs)) <$> unConj
  in (us, newEnv)
  where
    construct subst cs ls rs = ctr $ E.substitute subst $ ls ++ cs ++ rs

-- |Check if a goal has a recursive call.
isRec :: E.Env -> G S -> Bool
isRec env goal@(Invoke call _) =
  let (name, args, body) = E.envLookupDef env call in
  any ((== name) . getInvokeName) $ getInvokes body
  where
    getInvokes b = concat $ filter isInvoke <$> normalize b
isRec _ _ = False

unfoldAll :: E.Env -> Conj (G S) -> (E.Env, Conj (G S))
unfoldAll env = foldl' unfold' (env, [])
  where
    unfold' (env, goals) inv = (:goals) <$> unfold inv env

disunify :: E.Subst -> E.ConstrStore -> Ts -> Ts -> Maybe E.ConstrStore
disunify subst cs t1 t2 =
  let t1'    = E.substitute subst t1
      t2'    = E.substitute subst t2
      -- TODO: rewrite unify to return only new subst
      subst' = E.unify (Just subst) t1' t2'
      cs'    = flip E.sDiff subst <$> subst'
  in case cs' of
     Just []   -> Nothing
     Just cs'' -> Just $ cs'' ++ cs
     Nothing   -> Just cs

verifyCS :: E.Subst -> E.ConstrStore -> Maybe E.ConstrStore
verifyCS = go
  where
    go _ [] = Just []
    go subst (c@(v1, t2):cs) =
      let subst'  = E.unify (Just subst) (V v1) t2
          subst'' = flip E.sDiff subst <$> subst'
      in case subst'' of
            Nothing -> (c:) <$> go subst cs
            Just [] -> Nothing
            Just s  -> ((c:s) ++) <$> go subst cs

-- |Apply unifications and add some more of them.
unifyGoal :: E.Subst -> E.ConstrStore -> [G S] -> Maybe ([G S], E.Subst, E.ConstrStore)
unifyGoal subst cs = go subst cs [] where
  go subst cs conjs []                    = Just (reverse conjs, subst, cs)
  go subst cs conjs (g@(Invoke _ _) : gs) = go subst cs (g : conjs) gs
  go subst cs conjs ((t1 :=: t2):gs) = do
    subst' <- E.unify (Just subst) t1 t2
    cs'    <- verifyCS subst' cs
    go subst' cs' conjs gs
  go subst cs conjs ((t1 :#: t2):gs) =
   do
    cs' <- disunify subst cs t1 t2
    go subst cs' conjs gs


toScheme :: G X -> String
toScheme g =
  let (goal, defs) = P.takeOutLets g
      defsS = intercalate "\n" (toDefine <$> defs)
      goalS = toGoal goal
  in defsS ++ "\n" ++ goalS
  where
    toGoal goal =
       "(define test " ++ toS' goal ++ ")"

    toDefine (name, args, body) =
      "(define " ++ name ++ "\n" ++
      "   (lambda (" ++ intercalate " " args ++ ")\n" ++
      "   " ++ toS' body ++
      "\n   ))"


    toS' :: G X -> String
    toS' (t1 :=: t2) = "(== " ++ toST t1 ++ " " ++ toST t2 ++ ")"
    toS' (t1 :#: t2) = "(=/= " ++ toST t1 ++ " " ++ toST t2 ++ ")"
    toS' (g1 :/\: g2) = toS' g1 ++ " " ++ toS' g2
    toS' (g1 :\/: g2) = "(conde (" ++ toS' g1 ++ ") (" ++ toS' g2 ++ "))"
    toS' (Fresh x g) = "(fresh (" ++ x ++ ")" ++ toS' g ++ ")"
    toS' (Invoke name args) = "(" ++ name ++ " " ++ toSlist args ++ ")"

    toSlist args = intercalate " " (toST <$> args)

    toST (C "Nil" []) = "'()"
    toST (C "%" [h, hs]) = "`(" ++ toST' h ++ " . " ++ toST' hs ++ ")"
    toST (C "Cons" [h, hs]) = "`(" ++ toST' h ++ " . " ++ toST' hs ++ ")"
    toST (C "app" [r, l]) = "`(" ++ toST' r ++ "  " ++ toST' l ++ ")"
    toST (C "pair" [r, l]) = "`(" ++ toST' r ++ " . " ++ toST' l ++ ")"
    toST (C n []) = '\'' : n
    toST (C name term) = "`(" ++ name ++ " " ++ toSTlist term ++ ")"
    toST (V name) = name


    toST' (C "Nil" []) = "()"
    toST' (C "%" [h, hs]) = "(" ++ toST' h ++ " . " ++ toST' hs ++ ")"
    toST' (C "Cons" [h, hs]) = "(" ++ toST' h ++ " . " ++ toST' hs ++ ")"
    toST' (C "app" [r, l]) = "(" ++ toST' r ++ " " ++ toST' l ++ ")"
    toST' (C "pair" [r, l]) = "(" ++ toST' r ++ " . " ++ toST' l ++ ")"
    toST' (C n []) = '\'' : n
    toST' (C name term) = "(" ++ name ++ " " ++ toSTlist term ++ ")"
    toST' (V name) = ',' : name

    toSTlist terms = intercalate " " (toST' <$> terms)
