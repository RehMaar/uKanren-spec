{-# LANGUAGE TupleSections, RankNTypes #-}

module CpdMod.GlobalControlCA where
    

import qualified CPD
import           Syntax
import           Prelude                           hiding ( sequence )
import           Data.Maybe                               ( isJust )
import           Data.List                                ( find
                                                          , partition
                                                          , inits
                                                          )
import qualified Eval                          as E
import qualified Driving                       as D
import           Purification
import           Text.Printf
import           Debug.Trace
import qualified Data.Set                      as Set
import           Utils
import           DotPrinter
import           SldTreePrinter
import           Control.Arrow (first)
import qualified CpdMod.ChAtoms                as CA
import Embedding
import Data.Maybe


--trace' = trace
trace' :: String -> a -> a
--trace' = trace
trace' _ = id

type Descend = CPD.Descend

data GlobalTreeCh = LeafCh (Descend (CA.ChAtom S)) -- Node and its ancestors.
                           D.Generalizer
                           E.Sigma         -- Substitution for a tree.
                  | NodeCh (Descend (CA.ChAtom S)) -- Now its litteraly ChAtom!
                            D.Generalizer
                            CA.SldTreeInner     -- Its SLD Tree.
                            [GlobalTreeCh]  -- Its heirs.
                  | PruneCh (Descend (CA.ChAtom S)) -- Now its litteraly ChAtom!
                            D.Generalizer
                            CA.SldTreeInner     -- Its SLD Tree.

sizeGT :: GlobalTreeCh -> Integer
sizeGT (NodeCh _ _ _ ts) = 1 + sum (sizeGT <$> ts)
sizeGT _ = 1

depthGT :: GlobalTreeCh -> Integer
depthGT (NodeCh _ _ _ ts) = 1 + maximum (depthGT <$> ts)
depthGT _ = 1

instance Show GlobalTreeCh where
  show (LeafCh d _ s) = "Leaf (" ++ show s ++ ") { " ++ show d ++ "}"
  show (NodeCh f g _ tr) = "Node (" ++ show f ++ ") (" ++ show g ++ ") { " ++ show tr ++ "}"

goalToLogicGoal :: G X -> (CA.Atom S, E.Gamma, [S])
goalToLogicGoal goal = let
  (goal', defs) = takeOutLets goal
  gamma         = E.updateDefsInGamma E.env0 defs
  (gl, gm, ns)  = E.preEval' gamma goal'
  in ([gl], gm, ns)

resultants = fmap fst . CA.resultantsInner

isResultantSubst = CA.isResultantSubst

type Ancestors = Set (CA.ChAtom S)

--
-- **Definition**
--
-- For a global tree t, a node L, and a conjunction M define
-- generalize(t, L, M) =
--   let B in Seq_{\beta_L} such that B <| M & B != M
--       (M_1, M_2) = split_B(M)
--   in mcs(msg(M_1, B) \cup mcs(M_2))
--
-- Delta is from Gamma of Resultant
generalize :: CA.Atom S -> CA.Atom S -> E.Delta -> ([(CA.Atom S, D.Generalizer)], E.Delta)
generalize m b d =
  let ((m1, m2), genOrig, delta) = CPD.split d b m
      -- (generalized, _, gen, delta') = D.generalizeGoals d m1 b
  in  (((,genOrig) <$> CPD.mcs m1) ++ ((,[]) <$> CPD.mcs m2), delta)


-- initial splitting into maximally connected suconjunctions, may be something else
part' :: CA.Atom S -> [CA.Atom S]
part' = CPD.mcs

--
-- **Definition**
--
-- For a global tree t, a node L, and a conjunction M define
-- generalize(t, L, M) =
--   let B in Seq_{\beta_L} such that B <| M & B != M
--       (M_1, M_2) = split_B(M)
--   in mcs(msg(M_1, B) \cup mcs(M_2))
--
-- Delta is from Gamma of Resultant



whistleCA :: Set (CA.ChAtom S) -> CA.ChAtom S -> Maybe (CA.ChAtom S)
whistleCA ancs m = let res = find (\b -> embed b m && not (isVariant b m)) ancs
  in trace' ("\n\nWHISTLE:\n" ++ show (Set.filter (\b -> embed b m && not (isVariant b m)) ancs))
  res

-- Do we really need it?
type Abstracted = ([(CA.ChAtom S, D.Generalizer)], E.Delta)

data AbstractedChild = AbstractedChild {
  absSubst :: E.Sigma
  , absAtom :: CA.ChAtom S
  , absGen  :: D.Generalizer
  , absGamma :: E.Gamma
}

instance Show AbstractedChild where
  show ~(AbstractedChild subst atom gen _) = "{(" ++ show subst ++ ") (" ++ show atom ++ ") (" ++ show gen ++ ")}"

--
-- What happens with ChTree on splitting?
--
-- Our solution: generalize trees into one tree and
-- give it to each new atom.
--
--generalizeCA :: CA.ChAtom S -> CA.ChAtom S -> E.Delta -> Abstracted
generalizeCA env subst m b d =
  let atomB = CA.chAtom b
      atomM = CA.chAtom m
      delta = d
  in trace' ("\n!!!!!!\nGeneralize: " ++ show atomB ++ " " ++ show atomM ++ "\n") $ let
      ((m1, m2), gen, delta) = CPD.split d atomB atomM
      -- TODO: bad generalization
      res = CPD.mcs m1 ++ CPD.mcs m2
      ch1 = CA.atomToChAtom env subst m1
      genchtree = CA.msgChTrees [CA.chTree b, CA.chTree ch1]
      chatoms = (flip CA.ChAtom genchtree) <$> res
   in ((,gen) <$> chatoms, delta)

--
-- Вопросы:
--  * Как делать partition для chatom'а?
--    partition возвращает множество конъюнкций.
--    Как chtree на эти подконъюнкции разделяется?
--
--  > Сейчас просто раздаём им старое дерево.
--    Может, лучше считать?
abstractCA
  :: Set (CA.ChAtom S) -- The ancestors of a goal.
  -> CA.Resultant
  -> E.Delta           -- Set of used semantic variables
  -> Abstracted
abstractCA ancs (CA.Resultant subst goal env) d =
 trace' (printf "\n#############\nAbstracting \n%s\nDescend\n%s\n" (show goal) (show ancs)) $
 let parted = partition goal in trace' ("??????\nParted: " ++ show parted ++ "\n???????\n") $
 go ((,[]) <$> parted) d
 where
  chatom  = CA.atomToChAtom env subst goal

  -- Give a new chatom old chtree
  toChatom1 g = CA.ChAtom g (CA.chTree chatom)
  -- Compute a new chtree for an atom from paritioned set.
  toChatom2 = CA.atomToChAtom env subst

  partition = fmap toChatom2 . part'
  --partition g = (\g' -> toChatom2 [g']) <$> g

  go []              d@(x : _) = ([], d)
  go ((m, gen) : gs) d
    | Just b <- whistleCA ancs m =
          trace' ("\n&&&&&&\n" ++ show b ++ " embed " ++ show m ++ "\n********\n") $
          let (goals, delta) = generalizeCA env subst m b d
              goals' = case goals of
                         [(g, _)] | isVariant g m -> []
                         _ -> goals
          in  go (gs ++ goals') delta
    | otherwise = first ((m, gen):) (go gs d)

abstractChildCA
  :: Set (CA.ChAtom S)
  -> CA.Resultant
  -> ([AbstractedChild], E.Delta)
abstractChildCA ancs r@(CA.Resultant subst g env@(x, y, d))
  | (abstracted, delta) <- abstractCA ancs r d
  = (,delta) ((\(g, gen) -> AbstractedChild subst g gen (x, y, delta)) <$> abstracted)

--
-- 'Controlling Generalization ans Polyvariance in PD', p. 28.
-- 4.6. A Tree-Based Algorithm.
--
-- Abstraction algoritm:
--  B' = {chatom(B, P, U) | B \in leaves(A_n, t_n)}
--  While B' is not empty
--  * select chatom C A_b from B', remove it from B'
--  * H = {C A_C in Ancs of current node | C A_B embeds C A_C }
--  * If H is empty:
--    + add a new node with C A_B to the global tree as a child of the current node.
--  * Else if there's no such chatom C A_D in the tree that is an instance of C A_B
--    + insert into set B' msg(H \cup C A_B).
--

oneStep goal = let
  (lgoal, gamma, ns) = goalToLogicGoal goal
  tree = CA.sldResolutionAtom lgoal gamma E.s0
  chatom = CA.ChAtom lgoal (CA.sldToChTree tree)
  gt = go [chatom] [] gamma Set.empty chatom tree 
  in gt
  where
    go seen gen gamma ancs goal sld = let
         (substs, bodies) = partition isResultantSubst $ resultants sld
         abstracted = fst <$> abstractChildCA ancs <$> bodies
      in abstracted

conjToList [t1 :/\: t2] = [t1, t2]
conjToList t = t

topLevelCA :: G X -> (GlobalTreeCh, E.Gamma, [S])
topLevelCA goal = let
  (lgoal', gamma, ns) = goalToLogicGoal goal
  lgoal = conjToList lgoal'
  tree = CA.sldResolutionAtom lgoal gamma E.s0
  chatom = CA.ChAtom lgoal (CA.sldToChTree tree)
  gt = go [chatom] [] gamma Set.empty chatom tree E.s0 0
  in (gt, gamma, ns)
  where
{-    go :: [CA.ChAtom S]     -- Already seen atoms.
       -> D.Generalizer
       -> E.Gamma           -- 
       -> Set (CA.ChAtom S) -- Ancestors of the goal
       -> CA.ChAtom S       -- The goal
       -> CA.SldTreeInner   -- Sld of the goal
       -> GlobalTreeCh-}
    go seen gen gamma ancs goal sld subst lvl =
      if lvl >= 5 then PruneCh (CPD.Descend goal ancs) gen sld
      else
        let
             --
         -- Get the set of resultants from the SLD-tree and
         -- split it into `substs` (resultants of type `Success`)
         -- and `bodies` (resultants of type `Leaf`).
         --
         -- Resultant is the atom and its meta.
         --
         (substs, bodies) = partition isResultantSubst $ resultants sld
         --
         -- Abstract each body with the set of ancestors.
         --in trace "\nABS\n" $ let
         abstracted = fst <$> abstractChildCA ancs <$> bodies

         --in trace' ("\n>>>>>\nGOAL: " ++ show goal++
         --           "\nANCS: " ++ show (Set.map CA.chAtom ancs) ++
         --           "\nABS: " ++ show abstracted ++ "\n<<<<<<<\n") $
         --let

         --
         -- Split abtracted nodes into two list: nodes to unfold and other nodes
         --
         -- and seen goals which are new nodes to unfold.
         (unfoldNodes, otherNodes, newSeen) = foldl
           (\(unf, oth, see) gs ->
             let (var, new) = partition (\g -> CA.isSubst (absAtom g) || any (isVariant (absAtom g)) see) gs
             in
             --trace ("GS: " ++ show (absAtom <$> gs))
             --trace (concatMap (\ g -> "\n@@@\n" ++ (show $ (filter (CPD.isVariant (absAtom g))) see) ++ "\n@@@@@\n") gs)
             (unf ++ new, oth ++ var, (absAtom <$> new) ++ see)
           )
           ([], [], seen)
           abstracted
         --
         -- Add leaves
         --
         -- What chtree has substitution leaf?
         leaves' = (\(CA.Resultant sig atom _) ->
            LeafCh (CPD.Descend (CA.ChAtom atom (CA.ChRoot [])) newAncs) [] sig
           ) <$> substs
         -- TODO: Why ignore generalize?
         leaves = (\ach ->
            LeafCh (CPD.Descend (absAtom ach) newAncs)  [] (absSubst ach)
           ) <$> otherNodes

         -- Add current atom to new ancestors.
         newAncs = Set.insert goal ancs

         -- AbstractedChild -> GlobalTreeCh
         subtrees = (\(AbstractedChild subst chatom gen gamma) ->
            go newSeen gen gamma newAncs chatom (CA.sldResolutionAtom (CA.chAtom chatom) gamma subst) subst (succ lvl)
           ) <$> unfoldNodes

         sub = leaves ++ leaves' ++ subtrees
      in if null sub
         then LeafCh (CPD.Descend goal ancs) gen subst
         else NodeCh (CPD.Descend goal ancs) gen sld sub


-----
-----

topLevelCh' :: G X -> (GlobalTreeCh, CA.Atom S, [S])
topLevelCh' goal
  = let (logicGoal, gamma', names) = goalToLogicGoal goal
        globalTree =
          go [logicGoal] logicGoal Set.empty gamma' E.s0 []
    in
    (globalTree, logicGoal, names)
 where
  go :: [CA.Atom S] -> CA.Atom S -> Set (CA.ChAtom S)
                    -> E.Gamma -> E.Sigma -> D.Generalizer
                    -> GlobalTreeCh
  go nodes goal ancs gamma subst generalizer
    = let
        sldTreeInner = CA.sldResolutionAtom goal gamma E.s0
        sldTree      = CA.innerToSld sldTreeInner
        chTree       = CA.sldToChTree sldTreeInner
        atom         = CA.ChAtom goal chTree

        --
        -- How to use chtrees?
        --
        -- For resultants we don't have it!
        --
        -- How use them not for resultants?
        --
        (substs, bodies) = partition (null . snd3) ((\(CA.Resultant s a g) -> (s, a, Just g)) <$> resultants sldTreeInner)
        ancs' = Set.map CA.chAtom ancs
        abstracted =  abstractChild' ancs' <$> bodies

        (toUnfold, toNotUnfold, newNodes) = foldl
          (\(yes, no, seen) gs ->
            let (variants, brandNew) = partition (\(_, g, _, _) -> null g || any (isVariant g) seen) gs
            in  (yes ++ brandNew, no ++ variants, fmap snd4 brandNew ++ seen)
          )
          ([], [], nodes)
          abstracted

        substLeaves = forgetEnv substs
        leaves      = forgetStuff toNotUnfold
        smth =
          (\(subst, g, _) -> LeafCh (CPD.Descend (CA.ChAtom g (CA.ChRoot [])) Set.empty) [] subst)
            <$> (substLeaves ++ leaves)

        newAncs = Set.insert atom ancs
        ch =
          (\(subst, g, gen, env) -> go newNodes g newAncs env subst gen)
          <$> toUnfold
      in
      NodeCh (CPD.Descend atom ancs) generalizer sldTreeInner (smth ++ ch)

  forgetEnv   = fmap (\(x, y, _) -> (x, y, []))
  forgetStuff = fmap (\(x, y, gen, _) -> (x, y, gen))


whistle' :: Descend [G S] -> [G S] -> Maybe [G S]
whistle' descend m =
  let res = find (\b -> embed b m && not (isVariant b m))
                 (CPD.getAncs descend)
--  in  --trace (printf "Whistling\n%s\n%s" (show m) (show res)) $
  --in trace ("\n\nWHISTLE:\n" ++ show (Set.filter (\b -> CPD.embed b m && not (CPD.isVariant b m)) (CPD.getAncs descend)))
  in res

generalize' :: [G S] -> [G S] -> E.Delta -> ([([G S], D.Generalizer)], E.Delta)
generalize' m b d =
  let ((m1, m2), gen, delta) = CPD.split d b m
  in  (((,gen) <$> CPD.mcs m1) ++ ((,[]) <$> CPD.mcs m2), delta)

abstract'
  :: Descend (CA.Atom S) -- The goal with ancs
  -> CA.Atom S           -- The goal (from usage)
  -> E.Delta             -- Set of used semantic variables
  -> ([(CA.Atom S, D.Generalizer)], E.Delta)
abstract' descend goals d =
 --trace (printf "\nAbstracting \n%s\nDescend\n%s\n" (show goals) (show descend)) $
 go ((,[]) <$> part' goals) d
 where
  go []              d@(x : _) = ([], d)
  go ((m, gen) : gs) d
    | Just b <- whistle' descend m =
          let (goals, delta) = generalize m b d
              goals' = case goals of
                         [(goal, _)] | isVariant goal m -> []
                         _ -> goals
          in  go (gs ++ goals') delta
    | otherwise = first ((m, gen):) (go gs d)

abstractChild'
  :: Set (CA.Atom S)                     -- Ancestors of the goal
  -> (E.Sigma, CA.Atom S, Maybe E.Gamma) -- Body: the goal with subst and ctx
  -> [(E.Sigma, CA.Atom S, D.Generalizer, E.Gamma)]
abstractChild' _ (_, _, Nothing) = []
abstractChild' ancs (subst, g, Just env@(x, y, d))
  | (abstracted, delta) <- abstract' (CPD.Descend g ancs) g d
  = (\(g, gen) -> (subst, g, gen, (x, y, delta))) <$> abstracted
