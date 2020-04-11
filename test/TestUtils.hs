module TestUtils where

import System.Process (system)
import System.Exit (ExitCode)
import Data.Maybe
import Text.Printf

import PrettyPrint

import Syntax
import DotPrinter
import Utils
import Eval as E

import qualified Purification as P
import qualified OCanrenize as OC
import qualified Embedding as Emb

import qualified SC.Unfold.SeqUnfold as SU
import qualified SC.Unfold.FullUnfold as FU
import qualified SC.Unfold.RandUnfold as RU
import qualified SC.Unfold.NonRecUnfold as NU
import qualified SC.Unfold.RecUnfold as RecU
import qualified SC.Unfold.MaxUnfold as MaxU
import qualified SC.Unfold.MinUnfold as MinU
import qualified SC.SC as U
import qualified SC.SCInst as SCI

import qualified SC.DTree as DT
import qualified SC.DTResidualize as DTR

import qualified LogicInt as LI
import qualified List as L

import qualified Data.Set as Set
import Data.Monoid
import Data.List

--
-- Save a tree into pdf file.
--
printToPdf :: DotPrinter a => String -> a -> IO ExitCode
printToPdf name t = do
    let dotfilename = name ++ ".dot"
    let pdffilename = name ++ ".pdf"
    printTree dotfilename t
    system $ "dot -Tpdf '" ++ dotfilename ++ "' > '" ++ pdffilename ++ "'"

--
-- Open pdf file of a tree (using `zathura` pdf viewer).
--
openInPdf :: DotPrinter a => a -> IO ExitCode
openInPdf t = do
    let name = "/tmp/ukanrentesttree"
    openInPdfWithName name t

openInPdfWithName :: DotPrinter a => String -> a -> IO ExitCode
openInPdfWithName name t = do
    let dotfilename = name ++ ".dot"
    let pdffilename = name ++ ".pdf"
    printTree dotfilename t
    -- dot -Tpdf '$dot' > '$tmp_pdf_file'
    system $ "dot -Tpdf '" ++ dotfilename ++ "' > '" ++ pdffilename ++ "'"
    -- zathura '$pdf'
    system $ "zathura '" ++ pdffilename ++ "'"
    -- rm '$pdf' '$dot'
    system $ "rm '" ++ pdffilename ++ "' '" ++ dotfilename ++ "'"


--
-- OCanrenize
--

ocanren specMethod filename goal =
  ocanrenGen specMethod "topLevel" (filename ++ ".ml") goal

ocanrenResult filename topLevelName res =
  OC.topLevel filename topLevelName Nothing (pur res)
  where
    pur goal = let
        (tree, logicGoal, _) = goal
        (f, names) = DTR.topLevel tree
        (goal', names', defs) = P.purification (f, vident <$> names)
      in (goal', names', (\(n1, n2, n3) -> (n1, n2, fromJust $ DTR.simplify n3)) <$> defs)

ocanrenGen = ocanrenUltraGen Nothing

ocanrenUltraGen env specMethod topLevelName filename goal = do
  let p = pur goal
  OC.topLevel filename topLevelName env p
  where
    pur goal = let
        (tree, logicGoal, _) = specMethod goal
        (f, names) = DTR.topLevel tree
        (goal', names', defs) = P.purification (f, vident <$> names)
      in (goal', names', (\(n1, n2, n3) -> (n1, n2, fromJust $ DTR.simplify n3)) <$> defs)

ocanrenId specMethod filename goal = do
  let p = pur goal
  let name = filename ++ ".ml"
  OC.topLevel name "topLevel" Nothing p
  where
    pur goal = let
        (tree, logicGoal, _) = specMethod goal
        (f, names) = DTR.topLevel tree
        (goal', names', defs) = P.identity (f, vident <$> names)
      in (goal', names', (\(n1, n2, n3) -> (n1, n2, fromJust $ DTR.simplify n3)) <$> defs)

ocanrenWithoutSpec filename prg = do
  let fname = filename ++ ".ml"
  let (_, _, ns) = U.goalXtoGoalS prg
  let p@(g, n, d)  = P.justTakeOutLets (prg, vident <$> reverse ns)
  OC.topLevel fname "topLevel" Nothing p

{-
spec goal = let
    (tree, logicGoal, _) = NU.topLevel goal
    (f, names) = DTR.topLevel tree
    (goal', names', defs) = P.purification (f, vident <$> names)
    (g, a, d) = (goal', names', (\(n1, n2, n3) -> (n1, n2, fromJust $ DTR.simplify n3)) <$> defs)
  in foldl (flip Let) (fresh a g) d

specCPD goal =
  let (t, lg, n) = GC.topLevel goal
      f = CR.residualizationTopLevel t
      (gl, args, def) = P.purification (f, vident <$> reverse n)
  in foldl (flip Let) (fresh' args gl) def
  where
    fresh' [] g = g
    fresh' a g = fresh a g

ocanrenDoubleSpec goal = ocanrenWithoutSpec "a" $ spec $ spec goal
-}


{-
ocanrenPrint goal = do
  let p = pur goal
  putStrLn $ OC.ocanrenize' "topLevel" p
  where
    pur goal = let
        (tree, logicGoal, _) = SU.topLevel goal
        (f, names) = DTR.topLevel tree
        (goal', names', defs) = P.purification (f, vident <$> names)
      in (goal', names', (\(n1, n2, n3) -> (n1, n2, fromJust $ DTR.simplify n3)) <$> defs)
-}

--
-- DTree test utils
--
findGoal :: DT.DGoal -> DT.DTree -> Maybe DT.DTree
findGoal g t@(DT.Unfold ts _ g' _)
  | Emb.isVariant g g' = Just t
  | otherwise = getFirst $ mconcat $ (First . findGoal g) <$> ts
findGoal g t@(DT.Abs ts _ g' _)
  | Emb.isVariant g g'  = Just t
  | otherwise = getFirst $ mconcat $ (First . findGoal g) <$> ts
findGoal g (DT.Gen t _) = findGoal g t
findGoal g t@(DT.Renaming g' _ _ _)
  | Emb.isVariant g g' = Just t
findGoal _ _ = Nothing

--
-- Rand Unfold
--
{-
findBest whatToDo goal num step =
    checkTrees whatToDo $ (\seed -> (seed,) $ fst3 $ RU.topLevel seed goal) <$> [1, succ step .. num ]
  where
    checkTrees whatToDo = {- minimum .-} fmap (fmap (treeParam whatToDo))
    treeParam whatToDo tree =
      let (l, s, f) = DT.countLeafs tree
          n         = DT.countNodes tree
      in if whatToDo then l else n

findBestByNodes = findBest False
findBestByLeafs = findBest True
-}

--
-- Test methods
--
--
-- Tree statistic
--
statTree :: DT.DTree -> IO ()
statTree t = do
  let [d, l, s, f, n] = statTree' t
  putStrLn $ "Depth: " ++ show d ++ " Leafs: " ++ show l ++  " Success: " ++ show s ++ " Fail: " ++ show f ++ " Nodes: " ++ show n

statTree' :: DT.DTree -> [Int]
statTree' t = do
  let d = DT.countDepth t
  let (l, s, f) = DT.countLeafs t
  let n = DT.countNodes t
  [d, l, s, f, n]

statMTree :: DTR.MarkedTree -> IO ()
statMTree mt = do
  let [d, l, s, f, n, fn] = statMTree' mt
  putStrLn $ "Depth: " ++ show d ++ " Leafs: " ++ show l ++ " Fail: " ++ show f ++ " Success: " ++ show s ++ " Nodes: " ++ show n ++ " FunCallNodes: " ++ show fn

statMTree' :: DTR.MarkedTree -> [Int]
statMTree' t = do
  let d = DTR.countDepth t
  let (l, f, s) = DTR.countLeafs t
  let (n, fn) = DTR.countNodes t
  [d, l, f, s, n, fn]


statMethod goal name topLevel = do
  putStr $ "|" ++ name ++ "| "
  let xs = statTree' $ fst3 $ topLevel goal
  putStrLn $ unwords (intersperse "|" $ show <$> xs) ++ "|"


statMethods runner goal = do
  -- statMethod goal "RU  " (RU.topLevel 17)
  statMethod goal "NU  " (runner "NU")
  statMethod goal "MinU" (runner "MnU")
  statMethod goal "MaxU" (runner "MxU")
  statMethod goal "SU  " (runner "SU")
  statMethod goal "RecU" (runner "RU")
  statMethod goal "FstU" (runner "FstU")
  statMethod goal "FU  " (runner "FU")

statMethods1 = statMethods SCI.run1
statMethods2 = statMethods SCI.run2

statRandIO goal = do
  (t, g, ns) <- RU.topLevelIO goal
  statTree t
  return (t, g, ns)

{-statMMethods goal = do
  statMMethod goal "FU  " FU.topLevel
  statMMethod goal "SU  " SU.topLevel
--  statMMethod goal "RU  " (RU.topLevel 17)
  statMMethod goal "NU  " NU.topLevel
  statMMethod goal "RecU" RecU.topLevel
  statMMethod goal "MinU  " MinU.topLevel
  statMMethod goal "MaxU  " MaxU.topLevel
  where
    statMMethod goal name topLevel = do
      putStr $ name ++ ": "
      statMTree $ DTR.makeMarkedTree $ fst3 $ topLevel goal-}

----------
----------
----------
prune :: DT.DTree -> [DT.DGoal]
prune (DT.Prune g) = [g]
prune (DT.Unfold ts _ _ _) = concat $ prune <$> ts
prune (DT.Abs ts _ _ _) = concat $ prune <$> ts
prune (DT.Gen t _) = prune t
prune _ = []

leavesT :: DT.DTree -> [(Int, DT.DGoal)]
leavesT (DT.Success _) = []
leavesT DT.Fail        = []
leavesT (DT.Renaming _ _ _ _) = []
leavesT (DT.Unfold ts _ g _) = (1, g) : concat (leavesT <$> ts)
leavesT (DT.Abs ts _ g _) = (0, g) : concat (leavesT <$> ts)
leavesT (DT.Gen t _) = leavesT t

debug :: DT.DTree -> [DT.DTree]
debug (DT.Success _) = []
debug DT.Fail        = []
debug (DT.Renaming _ _ _ _) = []
debug (DT.Unfold ts _ g _) = concat (debug <$> ts)
debug (DT.Abs ts _ g _) = concat (debug <$> ts)
debug (DT.Gen t _) = debug t
debug dbg@(DT.Debug _ _ _ _) = [dbg]

findA :: DT.DGoal -> DT.DTree -> Maybe E.Subst
findA _ (DT.Success _)  = Nothing
findA _ DT.Fail         = Nothing
findA _ (DT.Renaming _ _ _ _) = Nothing
findA g (DT.Unfold ts _ _ _)  = getFirst $ mconcat $ First <$> (findA g <$> ts)
findA g' (DT.Abs ts s g _)  | g == g' = Just s
                       | otherwise = getFirst $ mconcat $ First <$> (findA g' <$> ts)
findA g (DT.Gen t _)    = findA g t

prunesAncs :: DT.DTree -> [(DT.DGoal, [DT.DGoal])]
prunesAncs = prunes' []
   where
     prunes' :: [DT.DGoal] -> DT.DTree -> [(DT.DGoal, [DT.DGoal])]
     prunes' ancs (DT.Prune goal) = [(goal, ancs)]
     prunes' ancs (DT.Unfold ts _ g _) = concatMap (prunes' (g:ancs)) ts
     prunes' ancs (DT.Abs ts _ g _) = concatMap (prunes' (g:ancs)) ts
     prunes' ancs (DT.Gen t _) = prunes' ancs t
     prunes' _ _ = []

leavesAncs :: DT.DTree -> [(DT.DGoal, [DT.DGoal])]
leavesAncs (DT.Renaming g a _ _) = [(g, Set.toList a)]
leavesAncs (DT.Unfold ts _ g _) = concatMap leavesAncs ts
leavesAncs (DT.Abs ts _ g _) = concatMap leavesAncs ts
leavesAncs (DT.Gen t _) = leavesAncs t
leavesAncs _ = []

--
-- Prints list of goal and it's ancestors
--
writeGoalAncs :: String -> [(DT.DGoal, [DT.DGoal])] -> IO ()
writeGoalAncs name ds = do
    let str = concat $ intersperse "\n" $ fmap (\(g, ancs) -> show g ++ ": " ++ show ancs) ds
    writeFile name str

printGoalAncs :: [(DT.DGoal, [DT.DGoal])] -> IO ()
printGoalAncs ds =
    putStrLn $ concat $ intersperse "\n" $ fmap (\(g, ancs) -> show g ++ ": " ++ show ancs) ds

--
-- Check if goal contains invokation of `name` relation.
--
containsInvoke :: String -> DT.DGoal -> Bool
containsInvoke name = any (\x -> getInvokeName x == name) . filter isInvoke

--
--
getInvokeName (Invoke s _) = s
isInvoke (Invoke _ _) = True
isInvoke _ = False
--
--

--
-- Ancestors of a goal in derivation tree must follow rules:
-- *
--
-- checkOrder :: DT.DGoal -> [DT.DGoal] -> Maybe (DT.DGoal, DT.DGoal)
checkOrder ancs =
  filter (not . null . snd) $
  fst $ foldr (\a (rs, as) -> ((a, filter (a Emb.<|) as) : rs, a : as)) ([], []) ancs

cutExcept :: [DT.DGoal] -> DT.DTree -> Maybe DT.DTree
cutExcept cs t@(DT.Prune goal)
 | goal `elem` cs = Just t
cutExcept cs t@(DT.Renaming goal _ _ _)
 | goal `elem` cs = Just t
cutExcept cs (DT.Gen t _) = cutExcept cs t
cutExcept cs (DT.Abs ts a b c) =
    (\x -> DT.Abs x a b c) <$> (weird_sequence $ cutExcept cs <$> ts)
cutExcept cs (DT.Unfold ts a b c) =
    (\x -> DT.Unfold x a b c) <$> (weird_sequence $ cutExcept cs <$> ts)
cutExcept cs _ = Nothing

cutLeaves :: DT.DTree -> Maybe DT.DTree
cutLeaves (DT.Gen t _) = cutLeaves t
cutLeaves t@(DT.Abs [] _ _ _) = Just t
cutLeaves t@(DT.Unfold [] _ _ _) = Just t
cutLeaves (DT.Abs ts a b c) =
    (\x -> DT.Abs x a b c) <$> (weird_sequence $ cutLeaves <$> ts)
cutLeaves (DT.Unfold ts a b c) =
    (\x -> DT.Unfold x a b c) <$> (weird_sequence $ cutLeaves <$> ts)
cutLeaves _ = Nothing


--
--
--
cutNotPruned :: DT.DTree -> Maybe DT.DTree
cutNotPruned t@(DT.Prune _) = Just t
cutNotPruned (DT.Gen t _) = cutNotPruned t
cutNotPruned (DT.Abs ts a b c) =
    (\x -> DT.Abs x a b c) <$> (weird_sequence $ cutNotPruned <$> ts)
cutNotPruned (DT.Unfold ts a b c) =
    (\x -> DT.Unfold x a b c) <$> (weird_sequence $ cutNotPruned <$> ts)
cutNotPruned _ = Nothing

-- TODO: find better way
weird_sequence :: [Maybe a] -> Maybe [a]
weird_sequence ts = 
 let a = fromJust <$> filter isJust ts
 in if null a then Nothing else Just a
