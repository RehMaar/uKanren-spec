{-
  Copyright 2019 Ekaterina Verbitskaia

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions are met:
  
  1. Redistributions of source code must retain the above copyright notice,
  this list of conditions and the following disclaimer.
  
  2. Redistributions in binary form must reproduce the above copyright notice,
  this list of conditions and the following disclaimer in the documentation
  and/or other materials provided with the distribution.
  
  3. Neither the name of the copyright holder nor the names of its contributors
  may be used to endorse or promote products derived from this software without
  specific prior written permission.
  
  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
  DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
  FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
  USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 
 
  Changed by Maria Kuklina.
-}


{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}

module CPD where

import Prelude hiding (lookup)
import Syntax
import qualified Eval as E
import Text.Printf
import Control.Monad
import Data.Maybe
import Data.List (find, nub, intersect, partition, subsequences, tails)
import Purification
import qualified Data.Map.Strict as Map
import Debug.Trace
import Data.List
import qualified Driving as D
import qualified Data.Set as Set
import Control.Applicative ((<|>))
import PrettyPrint

data Descend a = Descend { getCurr :: a, getAncs :: Set a } deriving (Eq, Show)

instance (PrettyPrint a) => PrettyPrint (Descend a) where
  pretty (Descend curr ancs) = printf "%s <- %s" (pretty curr) (prettyList $ Set.toList ancs)

type DescendGoal = Descend (G S)

data SldTree = Fail
             | Success E.Sigma
             | Or [SldTree] E.Sigma
             | Conj SldTree [DescendGoal] E.Sigma
             | Leaf [DescendGoal] E.Sigma E.Gamma

sldDepth :: SldTree -> Integer
sldDepth (Conj sld _ _) = 1 + sldDepth sld
sldDepth (Or slds _) = 1 + foldl (\acc sld -> max acc (sldDepth sld)) 0 slds
sldDepth _ = 1

sldLeafs :: SldTree -> Integer
sldLeafs (Or slds _) = sum (sldLeafs <$> slds)
sldLeafs (Conj sld _ _) = sldLeafs sld
sldLeafs _ = 1

topLevel :: G X -> SldTree
topLevel goal =
  let (goal', _, defs)           = justTakeOutLets (goal, [])
      gamma                      = E.updateDefsInGamma E.env0 defs
      (logicGoal, gamma', names) = E.preEval' gamma goal'
  in  sldResolutionStep [Descend logicGoal Set.empty] gamma' E.s0 Set.empty True

sldResolution :: [G S] -> E.Gamma -> E.Sigma -> SldTree
sldResolution goal gamma subst = sldResolutionStep
  (map (\x -> Descend x Set.empty) goal)
  gamma subst Set.empty True

select :: [DescendGoal] -> Maybe DescendGoal
select = find (\x -> isSelectable embed (getCurr x) (getAncs x))

selecter :: [DescendGoal] -> ([DescendGoal], [DescendGoal])
selecter gs = span (\x -> not $ isSelectable embed (getCurr x) (getAncs x)) gs

isSelectable :: Show a => (G a -> G a -> Bool) -> G a -> Set (G a) -> Bool
isSelectable emb goal ancs =
  (not (any (`emb` goal) ancs) || Set.null ancs)

substituteDescend s =
  map $ \(Descend g ancs) -> Descend (E.substituteGoal s g) ancs

extend :: E.Iota -> (X, Ts) -> E.Iota
extend = uncurry . E.extend

unfold :: G S -> E.Gamma -> (G S, E.Gamma)
unfold g@(Invoke f as) env@(p, i, d)
  | (_, fs, body) <- p f
  , length fs == length as
  = let i'            = foldl extend i (zip fs as)
        (g', env', _) = E.preEval' (p, i', d) body
    in  (g', env')
  | otherwise
  = error "Unfolding error: different number of factual and actual arguments"
unfold g env = (g, env)

selectNext :: [DescendGoal] -> Maybe ([DescendGoal], DescendGoal, [DescendGoal])
selectNext gs =
  let (ls, rs) = selecter gs
  in if null rs then Nothing else Just (ls, head rs, tail rs)

sldResolutionStep
  :: [DescendGoal] -> E.Gamma -> E.Sigma -> Set [G S] -> Bool -> SldTree
sldResolutionStep gs env@(p, i, d@(temp : _)) s seen isFirstTime
  | variantCheck (map getCurr gs) seen
  = Leaf gs s env
  | Just (ls, Descend g ancs, rs) <- selectNext gs
  = let (g', env') = unfold g env in go g' env' ls rs g ancs isFirstTime
  | otherwise
  = Leaf gs s env
 where
  go g' env' ls rs g ancs isFirstTime
    = let
        normalized = normalize g'
        unified    = mapMaybe (unifyStuff s) normalized
        newSeen    = Set.insert (map getCurr gs) seen
        newList xs = (ls ++ map (\x -> Descend x (Set.insert g ancs)) xs ++ rs)
        addDescends xs s = substituteDescend s (newList xs)
      in
        case unified of
          [] -> Fail
          ns | length ns == 1 || isFirstTime -> Or (step <$> ns) s
           where
            step (xs, s')
              | null xs && null rs
              = Success s'
              | otherwise
              = let newDescends = addDescends xs s'
                    cond = isFirstTime && length ns == 1
                    tree = sldResolutionStep newDescends env' s' newSeen cond
                in  Conj tree newDescends s'
          ns | not (null rs) -> maybe
            (Leaf gs s env)
            (\(ls', Descend nextAtom nextAtomsAncs, rs') ->
              let (g'', env'') = unfold nextAtom env
              in  go g''
                     env''
                     (ls ++ (Descend g ancs : ls'))
                     rs'
                     nextAtom
                     nextAtomsAncs
                     False
            )
            (selectNext rs)
          ns -> Leaf gs s env

normalize :: G S -> [[G S]]
normalize (f :\/: g) = normalize f ++ normalize g
normalize (f :/\: g) = (++) <$> normalize f <*> normalize g
normalize g@(Invoke _ _) = [[g]]
normalize g@(_ :=: _) = [[g]]
normalize _ = error "Unexpected goal type in normalization"

unifyStuff :: E.Sigma -> [G S] -> Maybe ([G S], E.Sigma)
unifyStuff state gs = go gs state [] where
  go []                    state conjs = Just (reverse conjs, state)
  go (g@(Invoke _ _) : gs) state conjs = go gs state (g : conjs)
  go ((t :=: u) : gs)      state conjs = do
    s <- E.unify  (Just state) t u
    go gs s conjs

bodies :: SldTree -> [[G S]]
bodies = leaves

leaves :: SldTree -> [[G S]]
leaves (Or disjs _)   = concatMap leaves disjs
leaves (Conj ch  _ _) = leaves ch
leaves (Leaf ds _ _)  = [map getCurr ds]
leaves _ = []

resultants :: SldTree -> [(E.Sigma, [G S], Maybe E.Gamma)]
resultants (Success s)     = [(s, [], Nothing)]
resultants (Or disjs _)    = concatMap resultants disjs
resultants (Conj ch _ _)   = resultants ch
resultants (Leaf ds s env) = [(s, map getCurr ds, Just env)]
resultants Fail            = []

mcs :: (Eq a, Show a) => [G a] -> [[G a]]
mcs []  = []
mcs [g] = [[g]]
mcs (g : gs) =
  let (con, non, _) = foldl
        (\(con, non, vs) x -> if null (vs `intersect` vars x)
          then (con, x : non, vs)
          else (x : con, non, nub $ vars x ++ vs)
        )
        ([g], [], vars g)
        gs
  in  reverse con : mcs (reverse non)

vars :: (Eq a, Show a) => G a -> [Term a]
vars (Invoke _ args) = nub $ concatMap getVars args
  where
    getVars (V v)    = [V v]
    getVars (C _ ts) = concatMap getVars ts
vars _ = []

msgExists gs hs | length gs == length hs =
  all
      (\x -> case x of
        (Invoke f _, Invoke g _) -> f == g
        _                        -> False
      )
    $ zip gs hs
msgExists _ _ = False

-- ordered subconjunctions of the proper length
subconjs :: [a] -> Int -> [[a]]
subconjs gs n = combinations n gs
  where
    combinations :: Int -> [a] -> [[a]]
    combinations 0 _ = [[]]
    combinations _ [] = []
    combinations n (x:xs) = (map (x:) (combinations (n-1) xs)) ++ (combinations n xs)

-- works for ordered subconjunctions
complementSubconjs :: (Instance a (Term a), Eq a, Ord a, Show a) => [G a] -> [G a] -> [G a]
complementSubconjs xs ys =
  go xs ys
   where
    go [] xs = xs
    go (x:xs) (y:ys) | x == y         = go xs ys
    go (x:xs) (y:ys) | isRenaming x y = go xs ys
    go (x:xs) (y:ys) | isInst x y     = go xs ys
    -- go (x:xs) (y:ys) | isInst y x     = go xs ys
    go xs (y:ys)                  = y : go xs ys
    go xs ys = error (printf "complementing %s by %s" (show xs) (show ys))


minimallyGeneral :: (Show a, Ord a) => [([G a], D.Generalizer)] -> ([G a], D.Generalizer)
minimallyGeneral xs =
    maybe (error "Empty list of best matching conjunctions") id $
    find (\x -> all (not . isStrictInst (fst x) . fst) xs) xs <|>
    listToMaybe (reverse xs)

--
-- **Definition**
--
-- Best matching conjunction
--
-- Let Q be a conj and L be a set of conjs. A bmc for Q in L
-- is a minimally general element of the set
--   bmc(Q, L) = { msg(Q, Q') | Q' in L and msg(Q, Q') exists }
--
bmc :: E.Delta -> [G S] -> [[G S]] -> ([([G S], D.Generalizer)],  E.Delta)
bmc d q [] = ([], d)
bmc d q (q':qCurly) | msgExists q q' =
  let (generalized, _, gen, delta) = D.generalizeGoals d q q' in
  let (gss, delta') = bmc delta q qCurly in
  ((generalized, gen) : gss, delta')
bmc d q (q':qCurly) = trace "why msg does not exist?!" $ bmc d q qCurly

--
-- **Definition**
--
-- Let Q = A_1 && .. && A_n,
--     Q' -- conjunction such that Q <| Q'.
-- Let L be the set of all ordered subconj Q'' of Q'
-- consiting of n atoms such that Q <| Q''.
--
-- Then split_Q(Q') us the pair (B, R) where
-- B = bmc(Q, L)
-- and
-- R is the ordered subconj of Q' such that Q' =_r B && R
--
split :: E.Delta -> [G S] -> [G S] -> (([G S], [G S]), D.Generalizer, E.Delta)
split d q q' = -- q <= q'
  let n = length q
      qCurly = filter (\q'' -> and $ zipWith embed q q'') $ subconjs q' n
      (bestMC, delta) = bmc d q qCurly
      (b, gen) = minimallyGeneral bestMC
  in ((b, if length q' > n then complementSubconjs b q' else []), gen, delta)

class AlwaysEmbeddable a => Homeo a where
  couple :: a -> a -> Bool
  diving :: a -> a -> Bool
  homeo  :: a -> a -> Bool
  homeo x y = couple x y || diving x y

instance Homeo (Term a) where
  couple (C n as) (C m bs) | n == m && length as == length bs =
    all (uncurry homeo) $ zip as bs
  couple _ _ = False

  diving v (C _ as) = any (homeo v) as
  diving _ _ = False

  homeo (V _) (V _) = True
  homeo x y = couple x y || diving x y

instance Homeo (G a) where
  couple goal@(Invoke f as) (Invoke g bs) | isAlwaysEmbeddable goal || f == g && length as == length bs =
    all (uncurry homeo) $ zip as bs
  couple _ _ = False

  diving _ _ = False

instance Homeo [G a] where
  couple = error "Coupling isn't defined for a list of goals"
  diving = error "Diving isn't defined for a list of goals"

  homeo gs hs =
    any (all (uncurry homeo) . zip gs) (subconjs hs (length gs))

class (Eq b) => Instance a b | b -> a where
  inst :: b -> b -> Map a (Term a) -> Maybe (Map a (Term a))

  isInst :: b -> b -> Bool
  isInst x y = isJust $ inst x y Map.empty

  isStrictInst :: b -> b -> Bool
  isStrictInst x y = isInst x y && not (isInst y x)

  isVariant :: b -> b -> Bool
  isVariant x y = x == y || isInst x y && isInst y x

  isRenaming :: b -> b -> Bool
  isRenaming x y =
    x == y || maybe False (all (\e -> case e of V _ -> True; _ -> False ) . Map.elems) (inst x y Map.empty)

  instanceCheck :: Foldable t => b -> t b -> Bool
  instanceCheck g = any (`isInst` g)

  variantCheck :: Foldable t => b -> t b -> Bool
  variantCheck g = any (isVariant g)

instance (Eq a, Ord a) => Instance a (Term a) where
  inst (V v) u subst =
    case Map.lookup v subst of
      Just w | u == w -> Just subst
      Just w -> Nothing
      Nothing -> Just $ Map.insert v u subst
  inst (C n as) (C m bs) subst
    | n == m,
      length as == length bs =
      foldl (\s (a, b) -> s >>= \s -> inst a b s) (Just subst) (zip as bs)
  inst _ _ _ = Nothing

instance (Eq a, Ord a) => Instance a (G a) where
  inst (Invoke f as) (Invoke g bs) subst
    | f == g
    , length as == length bs =
      foldl (\s (a, b) -> s >>= \s -> inst a b s) (Just subst) (zip as bs)
  inst _ _ _ = Nothing


instance (Eq a, Ord a) => Instance a [G a] where
  inst as bs subst
    | length as == length bs =
      foldl (\s (a, b) -> s >>= \s -> inst a b s) (Just subst) (zip as bs)
  inst _ _ _ = Nothing


class AlwaysEmbeddable a where
  isAlwaysEmbeddable :: a -> Bool

instance AlwaysEmbeddable (G a) where
  isAlwaysEmbeddable (Invoke f _) = f `elem` []
  isAlwaysEmbeddable _ = False

instance AlwaysEmbeddable [G a] where
  isAlwaysEmbeddable = null

instance AlwaysEmbeddable (Term a) where
  isAlwaysEmbeddable = const True

-- Strict homeomorphic embedding. Explore: use a variants check instead of the instance check.
class (Homeo b, Instance a b, Eq b) => Embed a b | b -> a where
  embed :: b -> b -> Bool
  embed g h = isAlwaysEmbeddable g || g == h || homeo g h && not (isStrictInst h g)

instance (Ord a, Eq a) => Embed a (G a)
instance (Ord a, Eq a) => Embed a [G a] where
  embed gs hs = any (and . zipWith embed gs) $ subconjs hs (length gs)
