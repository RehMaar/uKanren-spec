module PD where

import Syntax

import qualified Data.Set as Set
import qualified Eval as E
import qualified Driving as D
import qualified Purification as P
import qualified CPD
import qualified Embedding as Emb

import DotPrinter

import Utils
import Data.List
import Control.Arrow (first)
import Text.Printf

--
-- NOTE
--
-- Had to copy part of GlobalControl.hs, because PD differs from CPD
-- only in abstraction operator (as far as I understand).
--


data Tree = Leaf (CPD.Descend [G S]) D.Generalizer E.Sigma
          | Node (CPD.Descend [G S]) D.Generalizer CPD.SldTree [Tree]

instance DotPrinter Tree where
  labelNode t@(Node _ _ _ ch) i vs es ids = addChildren t ch i vs es ids
  labelNode t                 i vs es ids = addLeaf     t    i vs es ids

isLeaf (Leaf _ _ _) = True
isLeaf _ = False

instance Dot Tree where
  dot (Leaf gs _ s)  = printf "L <BR/> %s <BR/> %s" (show s) (dot $ CPD.getCurr gs)
  dot (Node gs gen _ _) = printf "N <BR/> %s <BR/> %s" (dot $ CPD.getCurr gs) (show gen)

abstract
  :: Set.Set [G S]
  -> (E.Sigma, [G S], Maybe E.Gamma)
  -> [(E.Sigma, [G S], D.Generalizer, E.Gamma)]
abstract ancs (subst, goal, Just env@(x, y, d)) =
  let (abstracted, delta) = abstract' goal ancs d
  in (\(g, gen) -> (subst, g, gen, (x, y, delta))) <$> abstracted
  where
    -- whistle :: Set [G S] -> [G S] -> Maybe [G S]
    whistle m =
      find (\b -> Emb.embed b m && not (Emb.isVariant b m))

    generalize d m b =
      let (goal, gen1, gen2, d') = D.generalizeGoals d m b
      in ([(goal, gen2)], d')

    -- abstract' :: [G S] -> Set [G S] -> Delta -> ([([G S], Gen)] , Delta)
    abstract' gs ancs d = go ((\g -> ([g], [])) <$> gs) d
      where
        go [] d@(x : _) = ([], d)
        go ((m, gen) : gs) d
          | Just b <- whistle m ancs = let
              (goals, delta) = generalize d m b
            in go (gs ++ goals) delta
          | otherwise = first ((m, gen):) (go gs d)

-- G X include goal and program
topLevel :: G X -> (Tree, G S, [S])
topLevel goal = let
  (goal', defs) = P.takeOutLets goal
  env = E.updateDefsInGamma E.env0 defs
  (lgoal, lenv, names) = E.preEval' env goal'
  in (go [[lgoal]] [lgoal] Set.empty lenv [], lgoal, names)
  where
    go nodes goal ancs env gen = let
        subst = E.s0
        sld = CPD.sldResolution goal env subst
        (substs, bodies) = partition (null . snd3) $ CPD.resultants sld
        abstracted = abstract ancs <$> bodies
        (toUnfold, toNotUnfold, newNodes) =
          foldl (\(yes, no, seen) gs ->
            let (var, new) = partition (\g -> null (snd4 g) || any (Emb.isVariant $ snd4 g) seen) gs
            in (yes ++ new, no ++ var, (snd4 <$> new) ++ seen))
            ([], [], nodes)
            abstracted
        newAncs = Set.insert goal ancs
        ch = (\(_, g, gen, env) -> go newNodes g newAncs env gen) <$> toUnfold
        forgetEnv = map (\(x, y, _) -> (x, y, []))
        forgetStuff = map (\(x, y, gen, _) -> (x,y, gen))
        substLeaves = forgetEnv substs
        leaves = forgetStuff toNotUnfold
      in Node (CPD.Descend goal ancs) gen sld
          (map (\(subst, g, gen) -> Leaf (CPD.Descend g Set.empty) gen subst) (substLeaves ++ leaves) ++ ch)
