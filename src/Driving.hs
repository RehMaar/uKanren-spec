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

module Driving where

import           Control.Exception.Base
import           Control.Monad          (mplus)
import           Data.Foldable
import           Data.List hiding (group, groupBy)
import qualified Data.Map.Strict        as Map
import           Data.Maybe
import qualified Data.Set               as Set
import           Debug.Trace
import qualified Eval                   as E
import           Stream
import           Syntax
import           Text.Printf
import           Utils

type Generalizer = E.Sigma

refine :: ([G S], Generalizer, Generalizer, [S]) ->  ([G S], Generalizer, Generalizer, [S])
refine msg@(g, s1, s2, d) =
  let similar1 = filter ((>1) . length) $ groupBy group s1 []
      similar2 = filter ((>1) . length) $ groupBy group s2 []
      sim1 = map (map fst) similar1
      sim2 = map (map fst) similar2
      toSwap = concatMap (\(x:xs) -> map (\y -> (y, V x)) xs) (sim1 `intersect` sim2)
      newGoal = E.substituteConjs toSwap g
      s2' = filter (\(x,_) -> notElem x (map fst toSwap)) s2
      s1' = filter (\(x,_) -> notElem x (map fst toSwap)) s1
  in (newGoal, s1', s2', d)
  where
    groupBy _ [] acc = acc
    groupBy p xs acc =
      let (similar, rest) = partition (p (head xs)) xs
      in assert (similar /= []) $ groupBy p rest (similar : acc)

    group x y = snd x == snd y

generalize :: [S] -> (Generalizer, Generalizer) -> [G S] -> [G S] -> ([G S], Generalizer, Generalizer, [S])
generalize d gg gs hs =
  (\(x, (y,z), t) -> (reverse x, y, z, t)) $
  foldl (\ (goals, s, vs) gh ->
           let ((g, s1, s2), vs') = generalizeCall vs s gh in
           (g:goals, (s1, s2), vs')
        )
        ([], gg, d)
        (zip gs hs)

generalizeCall d gg (Invoke f as, Invoke g bs) | f == g =
  let ((C _ cs, s1, s2), d') = generalizeTerm d gg (C "()" as, C "()" bs) in
  ((Invoke f cs, s1, s2), d')

generalizeTerm vs s@(s1, s2) (C m ms, C n ns) | m == n && length ms == length ns =
  let (gs, (s1, s2), vs') = foldl (\ (gs, s, vs) ts ->
                                        let ((g, s1, s2), vs') = generalizeTerm vs s ts in
                                        (g:gs, (s1, s2), vs')
                                  ) ([], s, vs) $ zip ms ns
  in
  ((C m $ reverse gs, s1, s2), vs')
generalizeTerm vs (s1, s2) (V x, V y) | x == y = ((V x, s1, s2), vs)
generalizeTerm (v:vs) (s1, s2) (t1, t2) = ((V v, (v, t1):s1, (v, t2):s2), vs)


generalizeGoals :: [S] -> [G S] -> [G S] -> ([G S], Generalizer, Generalizer, [S])
generalizeGoals s as bs =
  let res@(msg_, s1_, s2_, _) = refine $ generalize s ([], []) as bs in
  assert (map (substitute s2_) msg_ == bs &&
          map (substitute s1_) msg_ == as) $
  res

substitute :: E.Sigma -> G S -> G S
substitute s (t1 :=: t2  ) = E.substitute s t1 :=: E.substitute s t2
substitute s (g1 :/\: g2 ) = substitute s g1 :/\: substitute s g2
substitute s (g1 :\/: g2 ) = substitute s g1 :\/: substitute s g2
substitute s (Invoke f as) = Invoke f $ map (E.substitute s) as
