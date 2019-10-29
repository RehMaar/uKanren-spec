{-
  Copyright 2019 Ekaterina Verbitskya
  
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

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Syntax where

import Data.List
import Text.Printf

import Debug.Trace

import PrettyPrint

type X    = String -- Syntactic variables
type S    = Int    -- Semantic variables
type Name = String -- Names of variables/definitions

-- Terms
data Term v = V v | C String [Term v] deriving (Eq, Ord, Show)
type Tx     = Term X
type Ts     = Term S

toX :: Term S -> Term X
toX = (vident <$>)

vident = ('x' :) . show

instance Functor Term where
  fmap f (V v)    = V $ f v
  fmap f (C s ts) = C s $ map (fmap f) ts

-- Definitions
type Def = (Name, [Name], G X)

def :: Name -> [Name] -> G X -> Def
def = (,,)

instance {-# OVERLAPPING #-} Show Def where
  show (name, args, body) = printf "%s %s = %s" name (unwords args) (show body)

-- Goals
data G a =
    Term a :=: Term a
  | G a :/\: G a
  | G a :\/: G a
  | Fresh  Name (G a)
  | Invoke Name [Term a]
  | Let Def (G a) deriving (Eq, Ord, Show)

instance Functor G where
  fmap f (t :=: u)          = (f <$> t) :=:  (f <$> u)
  fmap f (g :/\: h)         = (f <$> g) :/\: (f <$> h)
  fmap f (g :\/: h)         = (f <$> g) :\/: (f <$> h)
  fmap f (Fresh name g)     = Fresh name (f <$> g)
  fmap f (Invoke name args) = Invoke name $ map (f <$>) args
  fmap f (Let def g)        = Let def (f <$> g)

freshVars :: [Name] -> G t -> ([Name], G t)
freshVars names (Fresh name goal) = freshVars (name : names) goal
freshVars names goal = (names, goal)

infix  8 :=:
infixr 7 :/\:
infixr 6 :\/:

infixr 7 &&&
infixr 6 |||
infix  8 ===

(===) :: Term a -> Term a -> G a
(===) = (:=:)

(|||) :: G a -> G a -> G a
(|||) = (:\/:)

(&&&) :: G a -> G a -> G a
(&&&) = (:/\:)


fresh :: [Name] -> G a -> G a
fresh xs g = foldr Fresh g xs

call :: Name -> [Term a] -> G a
call = Invoke

-- Free variables
fv :: Eq v => Term v -> [v]
fv t = nub $ fv' t where
  fv' (V v)    = [v]
  fv' (C _ ts) = concatMap fv' ts

fvg :: G X -> [X]
fvg = nub . fv'
 where
  fv' (t1 :=:  t2) = fv t1 ++ fv t2
  fv' (g1 :/\: g2) = fv' g1 ++ fv' g2
  fv' (g1 :\/: g2) = fv' g1 ++ fv' g2
  fv' (Invoke _ ts) = concatMap fv ts
  fv' (Fresh x g)   = filter (x /=) $ fv' g
  fv' (Let (_, _, _) g) = fv' g

subst_in_term :: Eq v => v -> Term v -> Term v -> Term v
subst_in_term v t t0@(V v0)     = if v == v0 then t else t0
subst_in_term v t    (C n args) = C n $ map (subst_in_term v t) args

subst_in_goal :: X -> Term X -> G X -> G X
subst_in_goal v t   (t1 :=:  t2)        = subst_in_term v t t1 === subst_in_term v t t2
subst_in_goal v t   (g1 :/\: g2)        = subst_in_goal v t g1 &&& subst_in_goal v t g2
subst_in_goal v t   (g1 :\/: g2)        = subst_in_goal v t g1 ||| subst_in_goal v t g2
subst_in_goal v t g@(Fresh n g')        = if v == n then g else Fresh n $ subst_in_goal v t g'
subst_in_goal v t   (Invoke n ts)       = Invoke n $ map (subst_in_term v t) ts
subst_in_goal v t   (Let (n, a, g1) g2) = Let (n, a, if elem v a then g1 else subst_in_goal v t g1) $ subst_in_goal v t g2

instance PrettyPrint Int where
    pretty = show

instance PrettyPrint String where
    pretty = show

instance PrettyPrint a => PrettyPrint (Term a) where
  pretty (V v) = printf "v.%s" (pretty v)
  pretty (C name ts) =
    case name of
      "nil" -> "[]"
      "%" -> let [h,t] = ts
                in printf "(%s : %s)" (pretty h) (pretty t)
      "Nil" -> "[]"
      "Cons" -> let [h,t] = ts
                in printf "(%s : %s)" (pretty h) (pretty t)
      x | (x == "s" || x == "S") && length ts == 1 -> printf "S(%s)" (pretty $ head ts)
      x | (x == "o" || x == "O") && null ts -> "O"
      _ -> case ts of
             [] -> name
             _  -> printf "C %s [%s]" name (intercalate ", " $ map pretty ts)

instance PrettyPrint a => PrettyPrint (G a) where
  pretty (t1 :=:  t2)               = printf "%s = %s" (pretty t1) (pretty t2)
  pretty (g1 :/\: g2)               = printf "(%s /\\ %s)" (pretty g1) (pretty g2)
  pretty (g1 :\/: g2)               = printf "(%s \\/ %s)" (pretty g1) (pretty g2)
  pretty (Fresh name g)             =
    let (names, goal) = freshVars [name] g in
    printf "fresh %s (%s)" (unwords (pretty <$> reverse names)) (pretty goal)
  pretty (Invoke name ts)           = printf "%s %s" name (unwords $ map (\x -> if ' ' `elem` x then printf "(%s)" x else x) $ map pretty ts)
  pretty (Let (name, args, body) g) = printf "let %s %s = %s in %s" name (unwords args) (pretty body) (pretty g)


class Dot a where
  dot :: a -> String

instance {-# OVERLAPPING #-} Dot String where
  dot = id

instance Dot Int where
  dot = show

instance (Dot a, Dot b) => Dot (a, b) where
  dot (x,y) = printf "(%s, %s)" (dot x) (dot y)

instance Dot a => Dot [a] where
  dot x = intercalate ", " (map dot x)

instance Dot a => Dot (Term a) where
  dot (V v) = printf "v<SUB>%s</SUB>" (dot v)
  dot (C name ts) =
    case name of
      "pair" -> "(" ++ intercalate "," (dot <$> ts) ++ ")"
      "nil" -> "[]"
      "%" -> let [h,t] = ts
                in printf "%s : %s" (dot h) (dot t)
      "Nil" -> "[]"
      "Cons" -> let [h,t] = ts
                in printf "%s : %s" (dot h) (dot t)
      x | (x == "s" || x == "S") && length ts == 1 -> printf "S(%s)" (dot $ head ts)
      x | (x == "o" || x == "O") && null ts -> "O"
      _ -> case ts of
             [] -> name
             _  -> printf "C %s [%s]" name (unwords $ map dot ts)

instance Dot a => Dot (G a) where
  dot (t1 :=:  t2)               = printf "%s = %s" (dot t1) (dot t2)
  dot (g1 :/\: g2)               = printf "(%s /\\ %s)" (dot g1) (dot g2)
  dot (g1 :\/: g2)               = printf "(%s \\/ %s)" (dot g1) (dot g2)
  dot (Fresh name g)             =
    let (names, goal) = freshVars [name] g in
    printf "fresh %s (%s)" (dot $ reverse names) (dot goal)
  dot (Invoke name ts)           = printf "%s(%s)" name (dot ts)
  dot (Let (name, args, body) g) = printf "let %s = %s in %s" name (unwords args) (dot body) (dot g)

instance {-# OVERLAPPING #-} Dot a => Dot [G a] where
  dot gs = intercalate " /\\ " (map dot gs)
