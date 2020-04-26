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

module Eval where

import           Control.Monad
import           Data.List
import           Syntax
import           Text.Printf

import qualified Data.Map.Strict as Map

class Substitution s where
  sEmpty  :: s
  sLookup :: S -> s -> Maybe Ts
  sInsert :: S -> Ts -> s -> s
  sDiff :: s -> s -> s

instance Substitution Subst where
  sEmpty = []
  sLookup = lookup
  sInsert a b s = (a, b) : s
  sDiff = (\\)

type MapSigma = Map.Map S Ts

instance Substitution MapSigma where
  sEmpty  = Map.empty
  sLookup = Map.lookup
  sInsert = Map.insert
  sDiff   = Map.difference

-- States
-- |Variables interpretation, whatever it is.
type Iota  = ([X], X -> Ts)
-- |Substitution
type Subst = [(S, Ts)]
-- |Constraints Store
type ConstrStore = [(S, Ts)]
-- |List of free semantic variables
type NameSupply = [S]
-- |Environment: definitions of relations, vars interpretation and name supply
data Env = Env { envDefs :: Map.Map Name Def, envIota :: Iota, envNS :: NameSupply }

envLookupDef (Env defs _ _) name
  | Just def <- Map.lookup name defs
  = def
  | otherwise
  = error $ "No such a defnition in environment: <" ++ name ++ ">"

instance Show Env where
  show (Env def _ ns) = "Env{" ++ show def ++ ", ns = " ++ show (head ns) ++ "}"

unifyG :: Substitution subst => (S -> Ts -> subst -> Bool) -> Maybe subst -> Ts -> Ts -> Maybe subst
unifyG _ Nothing _ _ = Nothing
unifyG f st@(Just subst) u v =
  unify' (walk u subst) (walk v subst)  where
    unify' (V u') (V v') | u' == v' = Just subst
    unify' (V u') (V v') = Just $ sInsert (min u' v') (V $ max u' v') subst
    unify' (V u') t
      | f u' t subst
      = return $ sInsert u' v subst
    unify' t (V v')
      | f v' t subst
      = return $ sInsert v' u subst
    unify' (C a as) (C b bs) | a == b && length as == length bs =
      foldl (\ st' (u', v') -> unifyG f st' u' v') st $ zip as bs
    unify' _ _ = Nothing

walk :: Substitution subst => Ts -> subst -> Ts
walk x@(V v') s
  | Just t <- sLookup v' s
  = walk t s
walk u' _ = u'

-- Unification
unify :: Substitution subst => Maybe subst -> Ts -> Ts -> Maybe subst
unify = unifyG (\s ts -> not . occursCheck s ts)
  where
    occursCheck :: Substitution subst => S -> Ts -> subst -> Bool
    occursCheck u' t s = 
      let t' = walk t s in
      case t' of
        V v' | v' == u' -> True 
        V _ -> False 
        C _ as -> any (\x -> occursCheck u' x s) as

-- occursCheck u' t s = if elem u' $ fv t then Nothing else s

unifySubsts :: Subst -> Subst -> Maybe Subst
unifySubsts one two =
    -- trace ("one: " ++ show one ++ "\ntwo: " ++ show two) $
    let maximumVar = max (findUpper one) (findUpper two) in
    let one' = manifactureTerm maximumVar one in
    let two' = manifactureTerm maximumVar two in
    unify (Just s0) one' two'
  where
    findUpper []  = 0
    findUpper lst = maximum $ map fst lst
    supplement upper lst = lst --  [(x, y) | x <- [0..upper], let y = maybe (V x) id (lookup x lst)]
    manifactureTerm upper subst = C "ManifacturedTerm" $ map snd $ supplement upper subst

unifyNoOccursCheck :: Substitution subst => Maybe subst -> Ts -> Ts -> Maybe subst
unifyNoOccursCheck = unifyG (\_ _ -> const False)

---- Interpreting syntactic variables
infix 9 <@>
(<@>) :: Iota -> Tx -> Ts
i <@> (V x) = app i x
i <@> (C c ts) = C c $ map (i<@>) ts

showInt :: Iota -> String
showInt (dom, f) = intercalate ", " $ map (\ x -> printf "%s -> %s" x (show $ f x)) dom

---- Extending variable interpretation
extend :: Iota -> X -> Ts -> Iota
extend (xs, i) x ts = (if x `elem` xs then xs else x : xs , \y -> if x == y then ts else i y)

emptyIota :: Iota
emptyIota = ([], error . printf "Empty interpretation on %s" . show)

app :: Iota -> X -> Ts
app (_, i) = i

-- Applying substitution
class Substitute a where
  substitute :: Subst -> a -> a

instance Substitute (Term S) where
  substitute s t@(V x) =
    case lookup x s of
      Just tx | tx /= t -> substitute s tx
      _                 -> t
  substitute s (C m ts) = C m $ map (substitute s) ts

instance Substitute (G S) where
  substitute s (Invoke name as) = Invoke name (map (substitute s) as)
  substitute _ g = error $ printf "We have only planned to substitute into calls, and you are trying to substitute into:\n%s" (show g)

instance Substitute [G S] where
  substitute = map . substitute

substituteConjs :: Subst -> [G S] -> [G S]
substituteConjs = substitute

---- Composing substitutions
o :: Subst -> Subst -> Subst
o sigma theta =
  case map fst sigma `intersect` map fst theta of
    [] -> map (fmap (substitute sigma)) theta ++ sigma
    _  -> error "Non-disjoint domains in substitution composition"

dotSigma :: Subst -> String
dotSigma s = printf " [ %s ] " (intercalate ", " (map (\(x,y) -> printf "%s &rarr; %s" (dot $ V x) (dot y)) s))

showSigma :: Subst -> String
showSigma s = printf " [ %s ] " (intercalate ", " (map (\(x,y) -> printf "%s &rarr; %s" (show $ V x) (show y)) s))

showSigma' :: Subst -> String
showSigma' s = printf " [ %s ] " (intercalate ", " (map (\(x,y) -> printf "%s -> %s" (show $ V x) (show y)) s))

-- Pre-evaluation
preEval' = preEval

preEval :: Env -> G X -> (G S, Env, [S])
preEval = go []
 where
  -- go vars g@(_, i, _) (t1 :=: t2)  = (i <@> t1 :=: i <@> t2, g, vars)
  go vars g (t1 :#: t2)  = let i = envIota g in (i <@> t1 :#: i <@> t2, g, vars)
  go vars g (t1 :=: t2)  = let i = envIota g in (i <@> t1 :=: i <@> t2, g, vars)
  go vars g (g1 :/\: g2) = let (g1', g' , vars' ) = go vars  g  g1
                               (g2', g'', vars'') = go vars' g' g2
                           in (g1' :/\: g2', g'', vars'')
  go vars g (g1 :\/: g2) = let (g1', g' , vars') = go vars  g  g1
                               (g2', g'', vars'') = go vars' g' g2
                           in (g1' :\/: g2', g'', vars'')
  -- go vars   (p, i, y : d') (Fresh x g') = go (y : vars) (p, extend i x (V y), d') g'
  go vars env (Fresh x g')
    | y : ns' <- envNS env
    = go (y:vars) env{envIota = extend (envIota env) x (V y), envNS = ns'} g'
  -- go vars g@(_, i, _) (Invoke f fs)  = (Invoke f (map (i <@>) fs), g, vars)
  go vars g (Invoke f fs) = (Invoke f (map (envIota g <@>) fs), g, vars)
  go vars e (Let    def g) = let (g', e', vars') = go vars e g in
                                       (Let def g', e', vars')

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

env0 :: Env
-- env0 = (error . printf "Empty environment on %s" . show, emptyIota, [0 ..])
env0 = Env Map.empty emptyIota [0..]

update :: Env -> Def -> Env
-- update (p, i, d) def'@(name, _, _) = (\ name' -> if name == name' then def' else p name', i, d)
update env@(Env defs _ _) def'@(name, _, _) = env{envDefs = Map.insert name def' defs}

updateDefsInGamma :: Env -> [Def] -> Env
updateDefsInGamma = foldl' update

s0 :: Subst
s0 = []
