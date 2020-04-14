module SC.DTResidualize where

import Syntax
import DotPrinter
import Embedding

import qualified SC.DTree as DT
import qualified Eval as E
import qualified Purification as P

import Data.List
import Utils
import Data.Maybe (isJust, fromMaybe, mapMaybe, fromJust, catMaybes)
import Data.Char
import Control.Arrow (first)

import qualified Data.Set as Set

import Debug.Trace
import Text.Printf

generateFreshName :: String -> Set.Set String -> String
generateFreshName n names =
  if n `notElem` names
  then n
  else until (`notElem` names) ('_' :) n

residualizeSubst :: E.Subst -> G X
residualizeSubst subst =
  foldl1 (&&&) $ map (\(s, ts) -> toX (V s) === toX ts) $ reverse subst

--
-- Marked Derivation Tree
--
-- `Bool` flag for `Abs` and `Unfold` constructors set to True
-- if some `Renaming` is a variant of one of these nodes.
--
data MarkedTree = Fail
  | Success E.Subst
  | Unfold  [MarkedTree] E.Subst DT.DGoal Bool
  | Abs [MarkedTree] E.Subst DT.DGoal Bool
  | Renaming DT.DGoal E.Subst
  | Gen MarkedTree E.Subst
  deriving Eq
--
-- Debug output.
--
instance Show MarkedTree where
  show Fail                  = "Fail"
  show (Success s)           = "{Success}"
  show (Unfold ts _ goal isVar)  = "{Unfold " ++ show isVar ++ "\n [" ++ concatMap show ts ++ "]\n}"
  show (Abs ts _ goal isVar) = "{Abs " ++ show isVar ++ "\n [" ++ concatMap show ts ++ "]\n}"
  show (Gen t s)             = "{Gen  " ++ show t ++ "\n}"
  show (Renaming g _)          = "{Renaming " ++ show g ++ "}"

--
-- Change to downscale the tree.
--
dotSigma _ = ""
--dotSigma = E.dotSigma

instance Dot MarkedTree where
  dot Fail = "Fail"
  dot (Success s)   = "Success <BR/> " ++ dotSigma s
  dot (Gen _ s)     = "Gen <BR/> Generalizer: " ++ dotSigma s
  dot (Abs _ s d f) = printf "Abs %s <BR/> Subst: %s <BR/> Goal: %s" (showF f) (dotSigma s) (dot d)
  dot (Unfold ts s d f) = printf "Unfold %s <BR/> Subst: %s <BR/> Goal: %s" (showF f) (dotSigma s) (dot d)
  dot (Renaming goal s) = printf "Renaming <BR/> Goal: %s <BR/> Subst: %s" (dot goal)  (dotSigma s)

showF True = "T"
showF _ = ""

instance DotPrinter MarkedTree where
  labelNode t@(Unfold ch _ _ _) = addChildren t ch
  labelNode t@(Abs ch _ _ _) = addChildren t ch
  labelNode t@(Gen ch _) = addChild t ch
  labelNode t = addLeaf t

-- (Renaming, Fail, Success)
countLeafs :: MarkedTree -> (Int, Int, Int)
countLeafs (Unfold ts _ _ _)  = foldl (\(n1, m1, k1) (n2, m2, k2) -> (n1 + n2, m1 + m2, k1 + k2)) (0, 0, 0) (countLeafs <$> ts)
countLeafs (Abs ts _ _ _) = foldl (\(n1, m1, k1) (n2, m2, k2) -> (n1 + n2, m1 + m2, k1 + k2)) (0, 0, 0) (countLeafs <$> ts)
countLeafs (Gen t _) = countLeafs t
countLeafs Fail        = (0, 1, 0)
countLeafs (Success _) = (0, 0, 1)
countLeafs (Renaming _ _)  = (1, 0, 0)

countDepth :: MarkedTree -> Int
countDepth (Unfold ts _ _ _) = 1 + foldl max 0 (countDepth <$> ts)
countDepth (Abs ts _ _ _) = 1 + foldl max 0 (countDepth <$> ts)
countDepth (Gen t _) = 1 + countDepth t
countDepth _ = 1

-- -> (Count of nodes, Count of calls)
countNodes :: MarkedTree -> (Int, Int)
countNodes (Unfold ts _ _ True)  = let (a, b) = foldl (\(a1, b1) (a2, b2) -> (a1 + a2, b1 + b2)) (0, 0) (countNodes <$> ts) in (a + 1, b + 1)
countNodes (Abs ts _ _ True) = let (a, b) = foldl (\(a1, b1) (a2, b2) -> (a1 + a2, b1 + b2)) (0, 0) (countNodes <$> ts) in (a + 1, b + 1)
countNodes (Unfold ts _ _ _)     = let (a, b) = foldl (\(a1, b1) (a2, b2) -> (a1 + a2, b1 + b2)) (0, 0) (countNodes <$> ts) in (a + 1, b)
countNodes (Abs ts _ _ _)    = let (a, b) = foldl (\(a1, b1) (a2, b2) -> (a1 + a2, b1 + b2)) (0, 0) (countNodes <$> ts) in (a + 1, b)
countNodes (Gen t _) = let (a, b) = countNodes t in (a + 1, b)
countNodes _ = (1, 0)

-- |Describes a call of a relation.
data Call = Call
    { callName :: Name
   -- ^Generated name for a relational call.
    , callArgs :: [S]
   -- ^TODO: ???
    , callOrigArgs :: [S]
   -- ^Original arguments of a call node.
    }
  deriving Show

makeMarkedTree :: DT.DTree -> MarkedTree
makeMarkedTree x = go x (DT.leaves x) x
  where
    go :: DT.DTree      -- |Root of the tree
       -> [DT.DGoal]    -- |Leaves of the tree (Only `Renaming` nodes)
       -> DT.DTree      -- |Currently traversed tree.
       -> MarkedTree
    go _     _     DT.Fail                  = Fail
    go _     _     (DT.Success s)           = Success s
    go root leaves (DT.Gen t s)             = Gen (go root leaves t) s
    go root leaves (DT.Renaming goal s) = Renaming goal s
    go root leaves (DT.Unfold ts s g)     =
      let isVar = any (`isVariant` g) leaves
          ts'   = go root leaves <$> ts
      in Unfold ts' s g isVar
    go root leaves (DT.Abs ts s g)        =
      let isVar = any (`isVariant` g) leaves
          ts'   = go root leaves <$> ts
      in Abs ts' s g isVar

-- |Get all variables from the given term.
getVarFromTerm :: Term x -> [Term x]
getVarFromTerm v@(V _) = [v]
getVarFromTerm (C _ vs) = concatMap getVarFromTerm vs

getSFromTerm :: Term S -> [S]
getSFromTerm (V v)    = [v]
getSFromTerm (C _ vs) = concatMap getSFromTerm vs

argsToS :: [Term S] -> [S]
argsToS = concatMap getSFromTerm

-- |Generate name for an invocation.
genCallName :: [G a] -> String
genCallName = nameToOCamlName . concat . toUpperTail . fmap toName . filter isInvoke
  where toName (Invoke g _) = g

-- |Return all arguments of the conj's invokes.
getArgs :: [G a] -> [Term a]
getArgs = concatMap getInvokeArgs . filter isInvoke


genCall :: [G S] -> Call
genCall = genCall' []

genCall' cs goal = let
    nameSet = Set.fromList ((\(_, Call name _ _) -> name) <$> cs)
    callName = genCallName goal
    name = nameToOCamlName $ generateFreshName callName  nameSet
    args = argsToS $ genArgs goal
    orig = argsToS $ getArgs goal
  in Call name args orig
  where
    generateFreshName :: Name -> Set.Set Name -> Name
    generateFreshName n names =
      if n `notElem` names
      then n
      else until (`notElem` names) ('_' :) n

genArgs :: Eq a => [G a] -> [Term a]
genArgs = nub . genArgs'

genArgs' = concatMap getVarFromTerm . getArgs


-- genArgsByOrig :: [S] -> [S] -> [G S] -> [Term S]
genArgsByOrig args orig goalArgs
  | Just ms <- mapTwoLists orig goalArgs
  = (\a -> fromMaybe (error $ "Couldn't find argument " ++ show a ++ " in original argument list") $ lookup a ms) <$> args
  | otherwise
  = error $ "\nUnable to match goal args and invoke args: Args = " ++ show args
             ++ " Orig = " ++ show orig
             ++ " GoalArgs = " ++ show goalArgs ++ "\n"

genInvokeByCall (Call name args orig) goal = let
     goalArgs = genArgs' goal
     invArgs = map toX $ genArgsByOrig args orig goalArgs
     in Invoke name invArgs

-- |Generate call signature
genLetSig :: Ord a => [G a] -> (Name, [Term a])
genLetSig goal = (genCallName goal, genArgs goal)

-- |Get arguments from the given invoke.
getInvokeArgs (Invoke _ ts) = ts
getInvokeArgs _ = []

-- |Capitalize tail of the list of strings.
toUpperTail :: [String] -> [String]
toUpperTail [] = []
toUpperTail (x:xs) = x : ((\(c:cs) -> toUpper c : cs) <$> xs)

-- |Check if the goal is an invocation
isInvoke (Invoke _ _) = True
isInvoke _ = False

-- |Collect all invocation from the derivation tree.
collectCallNames = go
  where
    go cs (Abs ts _ goal True)     = let c = (goal, genCall' cs goal) in foldl go (c:cs) ts
    go cs (Unfold  ts _ goal True) = let c = (goal, genCall' cs goal) in foldl go (c:cs) ts
    go cs (Unfold  ts _ _ _)       = foldl go cs ts
    go cs (Abs ts _ _ _)           = foldl go cs ts
    go cs (Gen t _)                = go cs t
    go cs _                        = cs

topLevel t = topLevel' $ cutFailedDerivations $ makeMarkedTree t
  where
    topLevel' Fail = error "How to residualize failed derivation?"
    topLevel' mt'@(Unfold f1 f2 goal f3) = let
      mt = rearrangeTree $ Unfold f1 f2 goal True
      cs = collectCallNames [] mt
      (defs, body) = res cs [] mt
      topLevelArgs = getArgsForPostEval cs goal
      in (foldDefs defs $ postEval topLevelArgs goal body, topLevelArgs)

getArgsForPostEval cs = callArgs . findCall cs
postEval names goal   = E.postEval' (vident <$> names)

foldDefs [] g = g
foldDefs xs g = foldr1 (.) xs g

foldGoals _ [] = error "Empty goals!"
foldGoals _ [g] = g
foldGoals f gs  = foldr1 f gs

res = go where
    -- Make a call and form a new definition.
    helper cs s ts subst goal foldf = let
        -- Collect the rest definitions and body off the call.
        (defs, goals) = unzip $ go cs (subst `union` s) <$> ts
        -- Finding a call.
        Call name args argsOrig = findCall cs goal
        -- Make a body of the call.
        argsS = vident <$> args
        body = E.postEval' argsS $ foldGoals foldf goals
        -- Form a definition.
        def = Let (name, argsS, body)
        --
        goalArgs = genArgs' goal
        iargs = map toX $ genArgsByOrig args argsOrig goalArgs
        diff  = subst \\ s
        goal' = applySubst diff $ Invoke name iargs

      in (def : concat defs, goal')


    go cs s (Unfold ts subst dg True) = helper cs s ts subst dg (:\/:)

    go cs s (Unfold ts subst dg _)    = let
        diff = subst \\ s
        un   = subst `union` s
        (defs, goals) = unzip $ go cs un <$> ts
      in (concat defs, applySubst diff $ foldGoals (:\/:) goals)

    -- If `Abs` is marked, call helper for making a relational call.
    go cs s (Abs ts subst dg True) = helper cs s ts subst dg (:/\:)
    -- If `Abs` isn't marked.
    go cs s (Abs ts subst dg _)    = let
        -- Substitutions we didn't add.
        diff = subst \\ s
        -- Substitutions we added.
        un   = subst `union` s
        (defs, goals) = unzip $ go cs un <$> ts
      in (concat defs, applySubst diff $ foldGoals (:/\:) goals)
    -- For `Gen` we just print generalizer before the rest of the body.
    go cs s (Gen t subst) = applySubst (subst \\ s) <$> go cs (s `union` subst) t
    -- For `Renaming` we just search for an invokation.
    go cs s (Renaming dg subst) =
        ([], applySubst (subst \\ s) $ findInvoke cs dg)
    -- `Success` node says that we found a successful substitution.
    -- Either
    go _ s  (Success subst)
      | null (subst \\ s) = ([], Invoke "success" [])
      | otherwise         = ([], residualizeSubst (subst \\ s))
    -- `Fail` node must not be encountered, but just in sake of totality
    -- add this case. <failure> has to be an OCanren function.
    go _ _ Fail = ([], Invoke "failure" [])

applySubst [] = id
applySubst diff = (residualizeSubst diff :/\:)

getGenTree (Gen t _) = t

groupAndChildren = groupBy (\a1 a2 -> isGenNode a1 && isGenNode a2 && (getGen a1 == getGen a2))
  where
    isGenNode (Gen _ _) = True
    isGenNode _ = False

    getGen (Gen _ gen) = gen

findCall cs goal = snd
  $ fromMaybe (error $ "No invocation for the leaf: " ++ show goal)
  $ find (isVariant goal . fst) cs

--
-- Find a call and generate `Invoke`.
--
findInvoke :: [([G S], Call)] -> [G S] -> G X
findInvoke cs goal = genInvokeByCall (findCall cs goal) goal

--
--
-- Build a mapping from the first list to the second one and
-- check its consistency.
--
mapTwoLists :: (Eq a, Eq b) => [a] -> [b] -> Maybe [(a, b)]
mapTwoLists l1 l2
  | length l1 == length l2
  = checkMap $ zip l1 l2
  | otherwise
  = Nothing
  where
    checkMap [] = Just []
    checkMap ms = foldr checkMap' (Just []) ms

    checkMap' m@(m1, m2) (Just as)
      | Just x <- lookup m1 as
      , x /= m2
      = Nothing
      | otherwise = Just (m:as)
    checkMap' _ _ = Nothing

-- За один шаг. Предполагаем, что всё строилось слева направо. В процессе прохода собираем список плохих помеченных `Unfold`
-- и каждый лист, который вариант плохого `Unfold`, обрабатывать как Fail.
cutFailedDerivations = fromMaybe Fail . fst . cfd Set.empty 
  where
    cfd :: Set.Set DT.DGoal -- *Плохие* узлы, которые привели только к Fail узлам.
        -> MarkedTree       -- Текущий узел
        -> (Maybe MarkedTree, Set.Set DT.DGoal) -- Новое поддерево и обновлённый список *плохих* узлов
    cfd gs Fail = (Nothing, gs)
    cfd gs t@(Success _) = (Just t, gs)
    cfd gs t@(Renaming goal _)
      | Just _ <- find (isVariant goal) gs
      = (Nothing, gs)
      | otherwise
      = (Just t, gs)
    cfd gs (Gen t s) = first (flip Gen s <$>) (cfd gs t)
    cfd gs (Unfold  ts f1 g True) = cfdCommon1 Unfold gs ts f1 g
    cfd gs (Abs ts f1 g True) = cfdCommon1 Abs gs ts f1 g
    cfd gs (Unfold  ts f1 g f3)   = cfdCommon2 Unfold  gs ts f1 g f3
    cfd gs (Abs ts f1 g f3)   = cfdCommon2 Abs gs ts f1 g f3

    cfdCommon1 ctr gs ts f1 g = let
        (mts, gs') = foldl foldCfd ([], gs) ts
        ts' = catMaybes (reverse mts)
      in if null ts' then (Nothing, Set.insert g gs') else (Just $ ctr ts' f1 g True, gs')

    cfdCommon2 ctr gs ts f1 f2 f3 = let
        (mts, gs') = foldl foldCfd ([], gs) ts
        ts' = catMaybes (reverse mts)
      in if null ts' then (Nothing, gs') else (Just $ ctr ts' f1 f2 f3, gs')

    foldCfd (ts, gs) t = first (:ts) (cfd gs t)


--
-- Names with not alphanum symbols are not allowed as a part of OCaml identifiers,
-- so we need to construct a new name without such limitiations.
--
nameToOCamlName :: String -> String
nameToOCamlName name@(n:ns)
  | firstCorrect n && all restCorrect name
  = name
  | otherwise
  = let newName@(n':_) = concatMap toAlpha name
  in if firstCorrect n' then newName else 'a' : newName
  where toAlpha :: Char -> String
        toAlpha c
          | restCorrect c = [c]
          | otherwise = show $ fromEnum c
        firstCorrect c = isAlpha c || c == '_'
        restCorrect c  = isAlphaNum c || c == '_' || c == '\''

simplifyPurified (n1, n2, n3) = (n1, n2, fromJust $ simplify n3)

--
-- Some optimizations, which Purification doesn't do.
--
simplify :: G X -> Maybe (G X)
simplify g@(t1 :=: t2)
  | t1 == t2
  = Nothing
  | otherwise
  = Just g
simplify (t1 :\/: t2) = let
    t1' = simplify t1
    t2' = simplify t2
  in case (t1', t2') of
     (Just t1'', Just t2'') -> Just $ t1'' :\/: t2''
     (_, Just t2'') -> Just t2''
     (Just t1'', _) -> Just t1''
     _              -> Nothing
simplify (t1 :/\: t2) = let
    t1' = simplify t1
    t2' = simplify t2
  in case (t1', t2') of
     (Just t1'', Just t2'') -> Just $ t1'' :/\: t2''
     (_, Just t2'') -> Just t2''
     (Just t1'', _) -> Just t1''
     _              -> Nothing
simplify (Fresh name t)
 | Just t' <- simplify t
 = Just $ Fresh name t'
simplify t@(Invoke _ _) = Just t
simplify (Let (name, args, g1) g2)
 | Just g1' <- simplify g1
 , Just g2' <- simplify g2
 = Just $ Let (name, args, g1) g2
simplify _ = Nothing

getV (V a) = a

toCutMTree = cutFailedDerivations . makeMarkedTree

-- |Rearrange goals (put a recursive call in the end)
rearrangeTree :: MarkedTree -> MarkedTree
rearrangeTree t@(Unfold _ _ g _) = go g t
  where
    go n (Unfold ts s g t)
      | hasRenamingOf n ts
      = let (renamings, rest) = partition isRenamingNode ts
            (relevant, irrelevant) = partition (isVariantNode n) renamings
            ts' = irrelevant ++ rest ++ relevant
        in Unfold ts' s g t
    go n (Unfold ts s g True) = Unfold (go g <$> ts) s g True
    go n (Unfold ts s g t) = Unfold (go n <$> ts) s g t

    go n (Abs ts s g t)
      | hasRenamingOf n ts
      = let (renamings, rest) = partition isRenamingNode ts
            (relevant, irrelevant) = partition (isVariantNode n) renamings
            ts' = irrelevant ++ rest ++ relevant
        in Abs ts' s g t
    go n (Abs ts s g True) = Abs (go g <$> ts) s g True
    go n (Abs ts s g t) = Abs (go n <$> ts) s g t

    go n (Gen t s) = Gen (go n t) s
    go _ t = t

    isRenamingNode Renaming{} = True
    isRenamingNode _ = False

    getGoal (Renaming g _) = g

    isVariantNode n = isVariant n . getGoal

    hasRenamingOf n = any id . fmap (isVariantNode n) . filter isRenamingNode
