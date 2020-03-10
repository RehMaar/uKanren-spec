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

{-# LANGUAGE TupleSections #-}

module Eval where

import Control.Monad
import Data.List
import Syntax
import Debug.Trace
import Text.Printf

-- States
type Iota  = ([X], X -> Ts)

showIota :: Iota -> String
showIota (dom, f) = intercalate ", " $ map (\ x -> printf "%s -> %s" x (show $ f x)) dom

type Sigma = [(S, Ts)]
type Delta = [S]
type P     = Name -> Def
type Gamma = (P, Iota, Delta)

unifyG :: (S -> Ts -> Maybe Sigma -> Maybe Sigma)
          -> Maybe Sigma -> Ts -> Ts -> Maybe Sigma
unifyG _ Nothing _ _ = Nothing
unifyG f st@(Just subst) u v =
  unify' (walk u subst) (walk v subst)  where
    unify' (V u') (V v') | u' == v' = Just subst
    unify' (V u') t = f u' t $ Just $ (u', v) : subst
    unify' t (V v') = f v' t $ Just $ (v', u) : subst
    unify' (C a as) (C b bs) | a == b && length as == length bs =
      foldl (\ st' (u', v') -> unifyG f st' u' v') st $ zip as bs
    unify' _ _ = Nothing

    walk x@(V v') s = maybe x (\t -> walk t s) (lookup v' s)
    walk u' _ = u'

-- Unification
unify :: Maybe Sigma -> Ts -> Ts -> Maybe Sigma
unify = unifyG occursCheck where
  occursCheck u' t s = if elem u' $ fv t then Nothing else s

unifyNoOccursCheck :: Maybe Sigma -> Ts -> Ts -> Maybe Sigma
unifyNoOccursCheck = unifyG (\_ _ -> id)

---- Interpreting syntactic variables
infix 9 <@>
(<@>) :: Iota -> Tx -> Ts
i <@> (V x) = app i x
i <@> (C c ts) = C c $ map (i<@>) ts

---- Extending variable interpretation
extend :: Iota -> X -> Ts -> Iota
extend (xs, i) x ts = (if x `elem` xs then xs else x : xs , \y -> if x == y then ts else i y)

emptyIota :: Iota
emptyIota = ([], error . printf "Empty interpretation on %s" . show)

app :: Iota -> X -> Ts
app (_, i) = i

---- Applying substitution
substitute :: Sigma -> Ts -> Ts
substitute s t@(V x) =
  case lookup x s of
    Just tx | tx /= t -> substitute s tx
    _ -> t
substitute s (C m ts) = C m $ map (substitute s) ts

substituteGoal :: Sigma -> G S -> G S
substituteGoal s (Invoke name as) = Invoke name (map (substitute s) as)
substituteGoal _ g = error $ printf "We have only planned to substitute into calls, and you are trying to substitute into:\n%s" (show g)

substituteConjs :: Sigma -> [G S] -> [G S]
substituteConjs s = map $ substituteGoal s


---- Composing substitutions
o :: Sigma -> Sigma -> Sigma
o sigma theta =
  case map fst sigma `intersect` map fst theta of
    [] -> map (\ (s, ts) -> (s, substitute sigma ts)) theta ++ sigma
    _  -> error "Non-disjoint domains in substitution composition"

dotSigma :: Sigma -> String
dotSigma s = printf " [ %s ] " (intercalate ", " (map (\(x,y) -> printf "%s &rarr; %s" (dot $ V x) (dot y)) s))

showSigma :: Sigma -> String
showSigma s = printf " [ %s ] " (intercalate ", " (map (\(x,y) -> printf "%s &rarr; %s" (show $ V x) (show y)) s))

showSigma' :: Sigma -> String
showSigma' s = printf " [ %s ] " (intercalate ", " (map (\(x,y) -> printf "%s -> %s" (show $ V x) (show y)) s))

-- Pre-evaluation
preEval' :: Gamma -> G X -> (G S, Gamma, [S])
preEval' = preEval []
 where
  preEval vars g@(_, i, _) (t1 :=: t2)    = (i <@> t1 :=: i <@> t2, g, vars)
  preEval vars g           (g1 :/\: g2)   = let (g1', g' , vars' ) = preEval vars  g  g1 in
                                            let (g2', g'', vars'') = preEval vars' g' g2 in
                                            (g1' :/\: g2', g'', vars'')
  preEval vars g           (g1 :\/: g2)   = let (g1', g' , vars')  = preEval vars  g  g1 in
                                            let (g2', g'', vars'') = preEval vars' g' g2 in
                                            (g1' :\/: g2', g'', vars'')
  preEval vars   (p, i, y : d') (Fresh x g') =
    preEval (y : vars) (p, extend i x (V y), d') g'
  preEval vars g@(_, i, _) (Invoke f fs)  = (Invoke f (map (i <@>) fs), g, vars)
  preEval vars e           (Let    def' g) = let (g', e', vars') = preEval vars e g in
                                             (Let def' g', e', vars')

postEval' :: [X] -> G X -> G X
postEval' as goal =
  let freshs = fvg goal \\ as in
  foldr Fresh (postEval (freshs ++ as) goal) freshs
  where
    postEval vars (Let (f, args, b) g) =
      Let (f, args, let freshs = (fvg b \\ args) \\ vars
                    in  foldr Fresh (postEval (vars ++ args ++ freshs) b) freshs) $ postEval vars g
    postEval vars (g1 :/\: g2) = postEval vars g1 :/\: postEval vars g2
    postEval vars (g1 :\/: g2) = postEval vars g1 :\/: postEval vars g2
    postEval _ g = g


env0 :: Gamma
env0 = (\ i -> error $ printf "Empty environment on %s" (show i), emptyIota, [0 ..])

update :: Gamma -> Def -> Gamma
update (p, i, d) def'@(name, _, _) = (\ name' -> if name == name' then def' else p name', i, d)

updateDefsInGamma :: Gamma -> [Def] -> Gamma
updateDefsInGamma = foldl update

s0 :: Sigma
s0 = []
