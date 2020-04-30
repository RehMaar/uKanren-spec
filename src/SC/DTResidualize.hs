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
residualizeSubst [] = Invoke "success" []
residualizeSubst subst =
  foldl1 (&&&) $ map (\(s, ts) -> toX (V s) === toX ts) $ reverse subst

residualizeCStore :: E.ConstrStore -> G X
residualizeCStore subst =
  foldl1 (&&&) $ map (\(s, ts) -> toX (V s) =/= toX ts) $ reverse subst

--
-- Marked Derivation Tree
--
-- `Bool` flag for `Abs` and `Unfold` constructors set to True
-- if some `Renaming` is a variant of one of these nodes.
--
data MarkedTree =
    Fail
  | Success E.Subst E.ConstrStore
  | Unfold  [MarkedTree] E.Subst E.ConstrStore DT.DGoal Bool
  | Abs [MarkedTree] E.Subst E.ConstrStore DT.DGoal Bool
  | Renaming DT.DGoal E.Subst E.ConstrStore
  | Gen MarkedTree E.Subst
  deriving Eq
--
-- Debug output.
--
instance Show MarkedTree where
  show Fail                       = "Fail"
  show (Success s _)              = "{Success}"
  show (Unfold ts _ _ goal isVar) = "{Unfold " ++ show isVar ++ "\n [" ++ concatMap show ts ++ "]\n}"
  show (Abs ts _ _ goal isVar)    = "{Abs " ++ show isVar ++ "\n [" ++ concatMap show ts ++ "]\n}"
  show (Gen t s)                  = "{Gen  " ++ show t ++ "\n}"
  show (Renaming g _ _)           = "{Renaming " ++ show g ++ "}"

--
-- Change to downscale the tree.
--
dotSigma _ = ""
--dotSigma = E.dotSigma

instance Dot MarkedTree where
  dot Fail = "Fail"
  dot (Success s _)   = "Success <BR/> " ++ dotSigma s
  dot (Gen _ s)     = "Gen <BR/> Generalizer: " ++ dotSigma s
  dot (Abs _ s c d f) = printf "Abs %s <BR/> Subst: %s <BR/> CS: $s <BR/> Goal: %s" (showF f) (dotSigma s) (dotSigma c) (dot d)
  dot (Unfold ts s c d f) = printf "Unfold %s <BR/> Subst: %s <BR/> CS: %s <BR/> Goal: %s" (showF f) (dotSigma s) (dotSigma c) (dot d)
  dot (Renaming goal s c) = printf "Renaming <BR/> Goal: %s <BR/> Subst: %s <BR/> CS: %s" (dot goal) (dotSigma s) (dotSigma c)

showF True = "T"
showF _ = ""

instance DotPrinter MarkedTree where
  labelNode t@(Unfold ch _ _ _ _) = addChildren t ch
  labelNode t@(Abs ch _ _ _ _) = addChildren t ch
  labelNode t@(Gen ch _) = addChild t ch
  labelNode t = addLeaf t

-- (Renaming, Fail, Success)
countLeafs :: MarkedTree -> (Int, Int, Int)
countLeafs (Unfold ts _ _ _ _)  = foldl (\(n1, m1, k1) (n2, m2, k2) -> (n1 + n2, m1 + m2, k1 + k2)) (0, 0, 0) (countLeafs <$> ts)
countLeafs (Abs ts _ _ _ _) = foldl (\(n1, m1, k1) (n2, m2, k2) -> (n1 + n2, m1 + m2, k1 + k2)) (0, 0, 0) (countLeafs <$> ts)
countLeafs (Gen t _)  = countLeafs t
countLeafs Fail       = (0, 1, 0)
countLeafs Success{}  = (0, 0, 1)
countLeafs Renaming{} = (1, 0, 0)

countDepth :: MarkedTree -> Int
countDepth (Unfold ts _ _ _ _) = 1 + foldl max 0 (countDepth <$> ts)
countDepth (Abs ts _ _ _ _)    = 1 + foldl max 0 (countDepth <$> ts)
countDepth (Gen t _)           = 1 + countDepth t
countDepth _ = 1

-- -> (Count of nodes, Count of calls)
countNodes :: MarkedTree -> (Int, Int)
countNodes (Unfold ts _ _ _ True) = let (a, b) = foldl (\(a1, b1) (a2, b2) -> (a1 + a2, b1 + b2)) (0, 0) (countNodes <$> ts) in (a + 1, b + 1)
countNodes (Abs ts _ _ _ True)    = let (a, b) = foldl (\(a1, b1) (a2, b2) -> (a1 + a2, b1 + b2)) (0, 0) (countNodes <$> ts) in (a + 1, b + 1)
countNodes (Unfold ts _ _ _ _)    = let (a, b) = foldl (\(a1, b1) (a2, b2) -> (a1 + a2, b1 + b2)) (0, 0) (countNodes <$> ts) in (a + 1, b)
countNodes (Abs ts _ _ _ _)       = let (a, b) = foldl (\(a1, b1) (a2, b2) -> (a1 + a2, b1 + b2)) (0, 0) (countNodes <$> ts) in (a + 1, b)
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
    go _     _     (DT.Success s c)           = Success s c
    go root leaves (DT.Gen t s)             = Gen (go root leaves t) s
    go root leaves (DT.Renaming goal s c) = Renaming goal s c
    go root leaves (DT.Unfold ts s c g)     =
      let isVar = any (`isVariant` g) leaves
          ts'   = go root leaves <$> ts
      in Unfold ts' s c g isVar
    go root leaves (DT.Abs ts s c g)        =
      let isVar = any (`isVariant` g) leaves
          ts'   = go root leaves <$> ts
      in Abs ts' s c g isVar

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
    go cs (Abs ts _ _ goal True)     = let c = (goal, genCall' cs goal) in foldl go (c:cs) ts
    go cs (Unfold  ts _ _ goal True) = let c = (goal, genCall' cs goal) in foldl go (c:cs) ts
    go cs (Unfold  ts _ _ _ _)       = foldl go cs ts
    go cs (Abs ts _ _ _ _)           = foldl go cs ts
    go cs (Gen t _)                  = go cs t
    go cs _                          = cs

topLevel t = topLevel' $ cutFailedDerivations $ makeMarkedTree t
  where
    topLevel' Fail = error "How to residualize failed derivation?"
    topLevel' mt'@(Unfold f1 f2 f4 goal f3) = let
      mt = rearrangeTree $ Unfold f1 f2 f4 goal True
      cs = collectCallNames [] mt
      (defs, body) = res cs [] [] mt
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
    helper cs s c ts subst cstore goal foldf = let
        -- Collect the rest definitions and body off the call.
        (defs, goals) = unzip $ go cs (subst `union` s) (cstore `union` c) <$> ts
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
        diffCS = cstore \\ c

        goal' = applySubst diff $ applyCStore diffCS $ Invoke name iargs

      in (def : concat defs, goal')


    go cs s c (Unfold ts subst cstore dg True) = helper cs s c ts subst cstore dg (:\/:)

    go cs s c (Unfold ts subst cstore dg _)    = let
        diff = subst \\ s
        un   = subst `union` s

        diffCS = cstore \\ c
        unCS   = cstore `union` c

        (defs, goals) = unzip $ go cs un unCS <$> ts
      in (concat defs, applySubst diff $ applyCStore diffCS $ foldGoals (:\/:) goals)

    -- If `Abs` is marked, call helper for making a relational call.
    go cs s c (Abs ts subst cstore dg True) = helper cs c s ts subst cstore dg (:/\:)
    -- If `Abs` isn't marked.
    go cs s c (Abs ts subst cstore dg _)    = let
        -- Substitutions we didn't add.
        diff = subst \\ s
        -- Substitutions we added.
        un   = subst `union` s

        diffCS = cstore \\ c
        unCS   = cstore `union` c

        (defs, goals) = unzip $ go cs un unCS <$> ts
      in (concat defs, applySubst diff $ applyCStore diffCS $ foldGoals (:/\:) goals)
    -- For `Gen` we just print generalizer before the rest of the body.
    go cs s c (Gen t subst) = applySubst (subst \\ s) <$> go cs (s `union` subst) c t
    -- For `Renaming` we just search for an invokation.
    go cs s c (Renaming dg subst cstore) =
        ([], applySubst (subst \\ s) $ applyCStore (cstore \\ c) $ findInvoke cs dg)
    -- `Success` node says that we found a successful substitution.
    -- Either
    go _ s c (Success subst cstore)
      | null (subst \\ s), null (cstore \\ c)       = ([], Invoke "success" [])
      | null (subst \\ s), not $ null (cstore \\ c) = ([], residualizeCStore (cstore \\ c))
      | not $ null (subst \\ s), null (cstore \\ c) = ([], residualizeSubst (subst \\ s))
      | otherwise = ([], residualizeSubst (subst \\ s) &&& residualizeCStore (cstore \\ c))

    -- `Fail` node must not be encountered, but just in sake of totality
    -- add this case. <failure> has to be an OCanren function.
    go _ _ _ Fail = ([], Invoke "failure" [])

applySubst [] = id
applySubst diff = (residualizeSubst diff :/\:)

applyCStore [] = id
applyCStore diff = (residualizeCStore diff :/\:)

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
    cfd gs t@(Success _ _) = (Just t, gs)
    cfd gs t@(Renaming goal _ _)
      | Just _ <- find (isVariant goal) gs
      = (Nothing, gs)
      | otherwise
      = (Just t, gs)
    cfd gs (Gen t s) = first (flip Gen s <$>) (cfd gs t)
    cfd gs (Unfold  ts f1 f2 g True) = cfdCommon1 Unfold gs ts f1 f2 g
    cfd gs (Abs ts f1 f2 g True) = cfdCommon1 Abs gs ts f1 f2 g
    cfd gs (Unfold  ts f1 f2 g f3)   = cfdCommon2 Unfold  gs ts f1 f2 g f3
    cfd gs (Abs ts f1 f2 g f3)   = cfdCommon2 Abs gs ts f1 f2 g f3

    cfdCommon1 ctr gs ts f1 f2 g = let
        (mts, gs') = foldl foldCfd ([], gs) ts
        ts' = catMaybes (reverse mts)
      in if null ts' then (Nothing, Set.insert g gs') else (Just $ ctr ts' f1 f2 g True, gs')

    cfdCommon2 ctr gs ts f1 c f2 f3 = let
        (mts, gs') = foldl foldCfd ([], gs) ts
        ts' = catMaybes (reverse mts)
      in if null ts' then (Nothing, gs') else (Just $ ctr ts' f1 c f2 f3, gs')

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
simplify g@(t1 :#: t2)
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
rearrangeTree t@(Unfold _ _ _ g _) = go g t
  where
    go n (Unfold ts s c g t)
      | hasRenamingOf n ts
      = let (renamings, rest) = partition isRenamingNode ts
            (relevant, irrelevant) = partition (isVariantNode n) renamings
            ts' = irrelevant ++ rest ++ relevant
        in Unfold ts' s c g t
    go n (Unfold ts s c g True) = Unfold (go g <$> ts) s c g True
    go n (Unfold ts s c g t) = Unfold (go n <$> ts) s c g t

    go n (Abs ts s c g t)
      | hasRenamingOf n ts
      = let (renamings, rest) = partition isRenamingNode ts
            (relevant, irrelevant) = partition (isVariantNode n) renamings
            ts' = irrelevant ++ rest ++ relevant
        in Abs ts' s c g t
    go n (Abs ts s c g True) = Abs (go g <$> ts) s c g True
    go n (Abs ts s c g t) = Abs (go n <$> ts) s c g t

    go n (Gen t s) = Gen (go n t) s
    go _ t = t

    isRenamingNode Renaming{} = True
    isRenamingNode _ = False

    getGoal (Renaming g _ _) = g

    isVariantNode n = isVariant n . getGoal

    hasRenamingOf n = or . fmap (isVariantNode n) . filter isRenamingNode
