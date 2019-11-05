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

module GlobalControl where
    
import qualified CPD
import Prelude hiding (sequence)
import Data.Maybe (isJust)
import Data.List (find, partition, inits, intercalate)
import qualified Data.Set as Set
import Control.Arrow (first)

import Text.Printf
import Debug.Trace

import Syntax
import Purification
import Embedding
import qualified Eval as E
import qualified Driving as D

import Utils
import DotPrinter
import SldTreePrinter

type Descend = CPD.Descend

data GlobalTree = Leaf  (Descend [G S]) D.Generalizer E.Sigma
                | Node  (Descend [G S]) D.Generalizer CPD.SldTree [GlobalTree]
                | Prune (Descend [G S]) E.Sigma

sequence :: Descend a -> Set a
sequence = CPD.getAncs

branch :: GlobalTree -> Set [G S]
branch (Leaf d _ _)   = sequence d
branch (Node d _ _ _) = sequence d

leaves :: GlobalTree -> Set [G S]
leaves (Leaf d _ _ ) = Set.singleton $ CPD.getCurr d
leaves (Node _ _ _ ch) =
  let sets = map leaves ch in
  foldr Set.union Set.empty sets

-- initial splitting into maximally connected suconjunctions, may be something else
part :: [G S] -> [[G S]]
part = CPD.mcs

abstract
  :: Descend [G S] -- The goal with ancs
  -> [G S]         -- The goal (from usage)
  -> E.Delta       -- Set of used semantic variables
  -> ([([G S], D.Generalizer)], E.Delta)
abstract descend goals d =
 go ((,[]) <$> part goals) d
 where
  go []              d@(x : _) = ([], d)
  go ((m, gen) : gs) d
    | Just b <- whistle descend m =
          let (goals, delta) = generalize m b d
              goals' = case goals of
                         [(goal, _)] | isVariant goal m -> []
                         _ -> goals
          in  go (gs ++ goals') delta
    | otherwise = first ((m, gen):) (go gs d)

whistle :: Descend [G S] -> [G S] -> Maybe [G S]
whistle descend m =
  find (\b -> embed b m && not (isVariant b m)) (sequence descend)

generalize :: [G S] -> [G S] -> E.Delta -> ([([G S], D.Generalizer)], E.Delta)
generalize m b d =
  let ((m1, m2), genOrig, delta) = CPD.split d b m in
  (map ((,genOrig)) (CPD.mcs m1) ++ map ((,[])) (CPD.mcs m2) , delta)

abstractChild
  :: Set [G S]                       -- Ancestors of the goal
  -> (E.Sigma, [G S], Maybe E.Gamma) -- Body: the goal with subst and ctx
  -> [(E.Sigma, [G S], D.Generalizer, E.Gamma)]
abstractChild _ (_, _, Nothing) = []
abstractChild ancs (subst, g, Just env@(x, y, d)) =
  let (abstracted, delta) = abstract (CPD.Descend g ancs) g d
  in  map (\(g, gen) -> (subst, g, gen, (x, y, delta))) abstracted

conjToList :: G a -> [G a]
conjToList (g :/\: h) = conjToList g ++ conjToList h
conjToList x@(Invoke _ _) = [x]
conjToList _ = error "This conjunction is not a list of calls"

topLevel :: G X -> (GlobalTree, G S, [S])
topLevel goal =
  let (goal', defs) = takeOutLets goal
      gamma = E.updateDefsInGamma E.env0 defs
      (logicGoal, gamma', names) = E.preEval' gamma goal'
      nodes = [[logicGoal]] in
  (go nodes (CPD.Descend [logicGoal] Set.empty) gamma' E.s0 [] [], logicGoal, names) where
    go nodes d@(CPD.Descend goal ancs) gamma subst defs generalizer =
      let subst = E.s0
          sldTree = CPD.sldResolution goal gamma subst in
      let (substs, bodies) = partition (null . snd3) $ CPD.resultants sldTree
          abstracted = map (abstractChild ancs) bodies
          (toUnfold, toNotUnfold, newNodes) =
            foldl (\ (yes, no, seen) gs ->
                    let (variants, brandNew) = partition (\(_, g, _, _) -> null g || any (isVariant g) seen) gs in
                    (yes ++ brandNew, no ++ variants, map snd4 brandNew ++ seen)
                  )
                  ([], [], nodes)
                  abstracted
          (def, newDefs) = undefined
          ch = map (\(subst, g, gen, env) -> go newNodes (CPD.Descend g (Set.insert goal ancs)) env subst newDefs gen) toUnfold
          forgetEnv = map (\(x, y, _) -> (x, y, []))
          forgetStuff = map (\(x, y, gen, _) -> (x,y, gen))
          substLeaves = forgetEnv substs
          leaves = forgetStuff toNotUnfold
      in Node d generalizer sldTree (map (\(subst, g, gen) -> Leaf (CPD.Descend g Set.empty) [] subst) (substLeaves ++ leaves) ++ ch)
