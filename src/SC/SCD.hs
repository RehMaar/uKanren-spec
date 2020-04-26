{-
Perfect Supercompiler
-}
module SC.SCD where

import Syntax
import Utils
import DotPrinter

import qualified Eval             as E
import qualified SC.SC            as SC
import qualified SC.DTree         as DT
import qualified SC.DTResidualize as DTR
import qualified Embedding        as Embed
import qualified OCanrenize as OC
import qualified Purification as P

import qualified Data.Set as Set
import Control.Exception (assert)
import Data.List (uncons, foldl', (\\), union)
import Data.Maybe (mapMaybe, fromJust)
import Text.Printf

import qualified LogicInt as LI
import qualified Bool     as B
import qualified List     as L

-- |Tree for disequality experiment.
data DTreeD a =
    Fail
  | Success E.Subst E.ConstrStore
  | Unfold [DTreeD a] E.Subst E.ConstrStore a
  | Abs [DTreeD a] E.Subst E.ConstrStore a
  | Renaming a E.Subst E.ConstrStore
  | Gen (DTreeD a) E.Subst
  deriving Show

type DTreeD' = DTreeD DT.DGoal

leaves (Gen t _) = leaves t
leaves (Unfold ts _ _ _) = concatMap leaves ts
leaves (Abs ts _ _ _) = concatMap leaves ts
leaves (Renaming g _ _) = [g]
leaves _ = []

instance DotPrinter DTreeD' where
  labelNode t@(Unfold ch _ _ _) = addChildren t ch
  labelNode t@(Abs ch _ _ _)    = addChildren t ch
  labelNode t@(Gen ch _)        = addChild t ch
  labelNode t = addLeaf t

--dotSigma _ = ""
dotSigma = E.dotSigma

instance Dot DTreeD' where
  dot Fail = "Fail"
  dot (Success s cs)       = "Success <BR/> " ++ dotSigma s ++ "<BR/> CS: " ++ show (dotSigma cs)
  dot (Gen _ s)            = printf "Gen <BR/> Generalizer: %s" (E.dotSigma s)
  dot (Abs _ s cs d)       = printf "Abs <BR/> Subst: %s <BR/> CS: %s <BR/> Goal: %s" (dotSigma s) (dotSigma cs) (dot d)
  dot (Unfold _ s cs d)    = printf "Unfold <BR/> Subst: %s <BR/> CS: %s <BR/> Goal: %s" (dotSigma s) (dotSigma cs) (dot d)
  dot (Renaming goal s cs) = printf "Renaming <BR/> Subst: %s <BR/> CS: %s <BR/> Goal: %s" (dotSigma s) (dotSigma cs) (dot goal)

supercompD :: G X -> (DTreeD DT.DGoal, G S, [S])
supercompD g = let
  (lgoal, lgamma, lnames) = SC.goalXtoGoalS g
  lgoal' = SC.normalize lgoal
  igoal = assert (length lgoal' == 1) $ initGoal (head lgoal')
  tree = fst3 $ derive igoal [] lgamma E.s0 [] Set.empty 1
  in (tree, lgoal, lnames)

derive goal ancs env subst cs seen d
  | emptyGoal goal
  = (Success subst cs, seen, SC.maxFreshVar env)
  | SC.checkLeaf (getGoal goal) seen
  = (Renaming (getGoal goal) subst cs, seen, SC.maxFreshVar env)
  | SC.isGen (getGoal goal) (Set.fromList ancs)
  , (aGoals, ns) <- SC.abstractL ancs (getGoal goal) $ E.envNS env
  , not $ SC.abstractSame aGoals (getGoal goal)
  =
    let
      rGoal = getGoal goal
      nAncs = rGoal : ancs
      nSeen = Set.insert rGoal seen
      nEnv = env{E.envNS = ns}
      (seen', trees, maxVarNum) =
        foldl
          (\(seen, ts, m) (goal, gen) ->
            let (t, seen'', mv) = derive (initGoal goal) nAncs (SC.fixEnv m nEnv) subst cs seen (succ d)
                t' = if null gen then t else Gen t gen
            in (seen'', t':ts, mv)
          )
          (nSeen, [], SC.maxFreshVar env)
          aGoals
      tree = Abs (reverse trees) subst cs rGoal
    in (tree, seen', maxVarNum)
  | otherwise
  = case unfoldStep goal env subst cs of
      ([], _) -> (Fail, seen, SC.maxFreshVar env)
      (uGoals, nEnv) -> let
          rGoal = getGoal  goal
          nAncs = rGoal : ancs
          nSeen = Set.insert rGoal seen
  
          (seen', trees, maxVarNum) =
            foldl
              (\(seen, ts, m) (subst, cs, goal) ->
                let (t, seen'', mv) = derive goal nAncs (SC.fixEnv m nEnv) subst cs seen (succ d)
                in (seen'', t:ts, mv)
              )
              (nSeen, [], SC.maxFreshVar nEnv)
              uGoals
          tree = Unfold (reverse trees) subst cs rGoal
        in (tree, seen', maxVarNum)

data SUGoal = SUGoal { suGoal :: DT.DGoal, suNum :: Int} deriving Show

emptyGoal = null . suGoal
getGoal = suGoal
initGoal = flip SUGoal 0

unfoldStep :: SUGoal -> E.Env -> E.Subst -> E.ConstrStore -> ([(E.Subst, E.ConstrStore, SUGoal)], E.Env)
unfoldStep (SUGoal dgoal idx) env subst cs = let
    (newIdx, (immut, conj, mut)) = splitGoal idx dgoal
    (newEnv, uConj) = SC.unfold conj env

    nConj = SC.goalToDNF uConj
    unConj = mapMaybe (SC.unifyGoal subst cs) nConj
    us = (\(conj, subst, cs) -> (subst, cs, ctrGoal subst immut conj mut newIdx)) <$> unConj
  in (us, newEnv)
  where
    ctrGoal subst immut cs mut newIdx = let
        goal = E.substitute subst $ immut ++ cs ++ mut
      in SUGoal goal newIdx

splitGoal _ [g] = (0, ([], g, []))
splitGoal idx gs = let
  (ls, rs) = splitAt idx gs
  in case uncons rs of
      Just (c, []) -> (idx, (ls, c, []))
      Just (c, rs) -> (succ idx, (ls, c, rs))
      Nothing -> splitGoal 0 gs

data MarkedTree =
    MTFail
  | MTSuccess E.Subst E.ConstrStore
  | MTUnfold  [MarkedTree] E.Subst E.ConstrStore DT.DGoal Bool
  | MTAbs [MarkedTree] E.Subst E.ConstrStore DT.DGoal Bool
  | MTRenaming DT.DGoal E.Subst E.ConstrStore
  | MTGen MarkedTree E.Subst
  deriving Eq

makeMTD :: DTreeD' -> MarkedTree
makeMTD x = go x (leaves x) x
  where
    go _     _     Fail              = MTFail
    go _     _     (Success s cs)    = MTSuccess s cs
    go root leaves (Gen t s)         = MTGen (go root leaves t) s
    go root leaves (Renaming goal s cs) = MTRenaming goal s cs
    go root leaves (Unfold ts s cs g)   =
      let isVar = any (`Embed.isVariant` g) leaves
          ts'   = go root leaves <$> ts
      in MTUnfold ts' s cs g isVar
    go root leaves (Abs ts s cs g)        =
      let isVar = any (`Embed.isVariant` g) leaves
          ts'   = go root leaves <$> ts
      in MTAbs ts' s cs g isVar

topLevel t = topLevel' $ makeMTD t
  where
    topLevel' MTFail = error "How to residualize failed derivation?"
    topLevel' mt@(MTUnfold f1 f2 f4 goal f3) = let
      cs = collectCallNames [] mt
      (defs, body) = res cs [] [] mt
      topLevelArgs = DTR.getArgsForPostEval cs goal
      in (DTR.foldDefs defs $ DTR.postEval topLevelArgs goal body, topLevelArgs)

    collectCallNames = go
      where
        go cs (MTAbs ts _ _ goal True)     = let c = (goal, DTR.genCall' cs goal) in foldl' go (c:cs) ts
        go cs (MTUnfold  ts _ _ goal True) = let c = (goal, DTR.genCall' cs goal) in foldl' go (c:cs) ts
        go cs (MTUnfold  ts _ _ _ _)       = foldl go cs ts
        go cs (MTAbs ts _ _ _ _)           = foldl go cs ts
        go cs (MTGen t _)                  = go cs t
        go cs _                            = cs

    -- Make a call and form a new definition.
    helper cns s c ts subst cstore goal foldf = let
        -- Collect the rest definitions and body off the call.
        (defs, goals) = unzip $ res cns (subst `union` s) (cstore `union` c) <$> ts
        -- Finding a call.
        DTR.Call name args argsOrig = DTR.findCall cns goal
        -- Make a body of the call.
        argsS = vident <$> args
        body = E.postEval' argsS $ DTR.foldGoals foldf goals
        -- Form a definition.
        def = Let (name, argsS, body)
        --
        goalArgs = DTR.genArgs' goal
        iargs = map toX $ DTR.genArgsByOrig args argsOrig goalArgs
        diff  = subst \\ s
        diffCS = cstore \\ c

        goal' = DTR.applyCStore diffCS $ DTR.applySubst diff $ Invoke name iargs

      in (def : concat defs, goal')


    res cns s c (MTUnfold ts subst cstore dg True) = helper cns s c ts subst cstore dg (:\/:)

    res cns s c (MTUnfold ts subst cstore dg _)    = let
        diff = subst \\ s
        un   = subst `union` s

        diffCS = cstore \\ c
        unCS = cstore `union` c

        (defs, goals) = unzip $ res cns un unCS <$> ts
      in (concat defs, DTR.applySubst diff $ DTR.applyCStore diffCS $ DTR.foldGoals (:\/:) goals)

    -- If `Abs` is marked, call helper for making a relational call.
    res cns s c (MTAbs ts subst cstore dg True) = helper cns s c ts subst cstore dg (:/\:)
    -- If `Abs` isn't marked.
    res cns s c (MTAbs ts subst cstore dg _)    = let
        -- Substitutions we didn't add.
        diff = subst \\ s
        -- Substitutions we added.
        un   = subst `union` s

        diffCS = cstore \\ c
        unCS = cstore `union` c

        (defs, goals) = unzip $ res cns un unCS <$> ts
      in (concat defs, DTR.applySubst diff $ DTR.applyCStore diffCS $ DTR.foldGoals (:/\:) goals)
    -- For `Gen` we just print generalizer before the rest of the body.
    res cns s c (MTGen t subst) = DTR.applySubst (subst \\ s) <$> res cns (s `union` subst) c t
    -- For `Renaming` we just search for an invokation.
    res cns s c (MTRenaming dg subst cstore) =
        ([], DTR.applySubst (subst \\ s) $ DTR.applyCStore (cstore \\ c) $ DTR.findInvoke cns dg)
    -- `Success` node says that we found a successful substitution.
    -- Either
    res _ s c (MTSuccess subst cstore)
      | null (subst \\ s), null (cstore \\ c)             = ([], Invoke "success" [])
      | null (subst \\ s), not $ null (cstore \\ c)       = ([], DTR.residualizeCStore (cstore \\ c))
      | not $ null (subst \\ s), null (cstore \\ c)       = ([], DTR.residualizeSubst (subst \\ s))
      | otherwise = ([], DTR.residualizeSubst (subst \\ s) &&& DTR.residualizeCStore (cstore \\ c))
    -- `Fail` node must not be encountered, but just in sake of totality
    -- add this case. <failure> has to be an OCanren function.
    res _ _ _ MTFail = ([], Invoke "failure" [])

ocanrenD filename goal = do
  let p = pur goal
  OC.topLevel filename "topLevel" Nothing p
  where
    pur goal = let
        (tree, logicGoal, _) = supercompD goal
        (f, names) = topLevel tree
        (goal', names', defs) = P.purification (f, vident <$> names)
      in (goal', names', (\(n1, n2, n3) -> (n1, n2, fromJust $ DTR.simplify n3)) <$> defs)
