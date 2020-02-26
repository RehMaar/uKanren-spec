module TestUtils where

import System.Process (system)
import System.Exit (ExitCode)
import Data.Maybe
import Text.Printf

import PrettyPrint

import Syntax
import DotPrinter
import CPD.SldTreePrinter
import CPD.GlobalTreePrinter
import Utils
import Eval as E

import qualified CPD.LocalControl as CPD
import qualified CPD.CpdResidualization as CR
import qualified CPD.GlobalControl as GC
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

import qualified SC.DTree as DT
import qualified SC.DTResidualize as DTR

import qualified LogicInt as LI
import qualified List as L

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
  OC.topLevel name "topLevelSU" Nothing p
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


ocanrenSU = ocanren SU.topLevel
ocanrenFU = ocanren FU.topLevel
ocanrenRU seed = ocanren (RU.topLevel seed)

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

ocanrenCPD filename goal = do
  let (t, lg, n) = GC.topLevel goal
  let f = CR.residualizationTopLevel t
  let p = P.purification (f, vident <$> reverse n)
  let name = printf "%s.ml" filename
  OC.topLevel name "topLevelCPD" Nothing p

ocanrenPrint goal = do
  let p = pur goal
  putStrLn $ OC.ocanrenize' "topLevel" p
  where
    pur goal = let
        (tree, logicGoal, _) = SU.topLevel goal
        (f, names) = DTR.topLevel tree
        (goal', names', defs) = P.purification (f, vident <$> names)
      in (goal', names', (\(n1, n2, n3) -> (n1, n2, fromJust $ DTR.simplify n3)) <$> defs)

--
-- DTree test utils
--
findGoal :: DT.DGoal -> DT.DTree -> Maybe DT.DTree
findGoal g t@(DT.Or ts _ g')
  | Emb.isVariant g (CPD.getCurr g') = Just t
  | otherwise = getFirst $ mconcat $ (First . findGoal g) <$> ts
findGoal g t@(DT.And ts _ g')
  | Emb.isVariant g (CPD.getCurr g')  = Just t
  | otherwise = getFirst $ mconcat $ (First . findGoal g) <$> ts
findGoal g (DT.Gen t _) = findGoal g t
findGoal g t@(DT.Leaf g' _ _)
  | Emb.isVariant g (CPD.getCurr g') = Just t
findGoal _ _ = Nothing

--
-- Rand Unfold
--
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


statMethods goal = do
  statMethod goal "RU  " (RU.topLevel 17)
  statMethod goal "NU  " NU.topLevel
  statMethod goal "MinU" MinU.topLevel
  statMethod goal "MaxU" MaxU.topLevel
  statMethod goal "SU  " SU.topLevel
  statMethod goal "RecU" RecU.topLevel
  statMethod goal "FU  " FU.topLevel

statRandIO goal = do
  (t, g, ns) <- RU.topLevelIO goal
  statTree t
  return (t, g, ns)

statMMethods goal = do
  statMMethod goal "FU  " FU.topLevel
  statMMethod goal "SU  " SU.topLevel
  statMMethod goal "RU  " (RU.topLevel 17)
  statMMethod goal "NU  " NU.topLevel
  statMMethod goal "RecU" RecU.topLevel
  statMMethod goal "MinU  " MinU.topLevel
  statMMethod goal "MaxU  " MaxU.topLevel
  where
    statMMethod goal name topLevel = do
      putStr $ name ++ ": "
      statMTree $ DTR.makeMarkedTree $ fst3 $ topLevel goal

----------
----------
----------
prune :: DT.DTree -> [DT.DGoal]
prune (DT.Prune g) = [g]
prune (DT.Or ts _ _) = concat $ prune <$> ts
prune (DT.And ts _ _) = concat $ prune <$> ts
prune (DT.Gen t _) = prune t
prune _ = []

leavesT :: DT.DTree -> [(Int, DT.DDescendGoal)]
leavesT (DT.Success _) = []
leavesT DT.Fail        = []
leavesT (DT.Leaf _ _ _) = []
leavesT (DT.Or ts _ g) = (1, g) : concat (leavesT <$> ts)
leavesT (DT.And ts _ g) = (0, g) : concat (leavesT <$> ts)
leavesT (DT.Gen t _) = leavesT t

debug :: DT.DTree -> [DT.DTree]
debug (DT.Success _) = []
debug DT.Fail        = []
debug (DT.Leaf _ _ _) = []
debug (DT.Or ts _ g) = concat (debug <$> ts)
debug (DT.And ts _ g) = concat (debug <$> ts)
debug (DT.Gen t _) = debug t
debug dbg@(DT.Debug _ _ _ _) = [dbg]

findA :: DT.DGoal -> DT.DTree -> Maybe E.Sigma
findA _ (DT.Success _)  = Nothing
findA _ DT.Fail         = Nothing
findA _ (DT.Leaf _ _ _) = Nothing
findA g (DT.Or ts _ _)  = getFirst $ mconcat $ First <$> (findA g <$> ts)
findA g' (DT.And ts s g)  | CPD.getCurr g == g' = Just s
                       | otherwise = getFirst $ mconcat $ First <$> (findA g' <$> ts)
findA g (DT.Gen t _)    = findA g t

prunesAncs :: DT.DTree -> [(DT.DGoal, [DT.DGoal])]
prunesAncs = prunes' []
   where
     prunes' :: [DT.DGoal] -> DT.DTree -> [(DT.DGoal, [DT.DGoal])]
     prunes' ancs (DT.Prune goal) = [(goal, ancs)]
     prunes' ancs (DT.Or ts _ g) = concatMap (prunes' ((CPD.getCurr g):ancs)) ts
     prunes' ancs (DT.And ts _ g) = concatMap (prunes' ((CPD.getCurr g):ancs)) ts
     prunes' ancs (DT.Gen t _) = prunes' ancs t
     prunes' _ _ = []

leavesAncs :: DT.DTree -> [(DT.DGoal, [DT.DGoal])]
leavesAncs = leaves []
   where
     leaves :: [DT.DGoal] -> DT.DTree -> [(DT.DGoal, [DT.DGoal])]
     leaves ancs (DT.Leaf g _ _) = [(CPD.getCurr g, ancs)]
     leaves ancs (DT.Or ts _ g) = concatMap (leaves ((CPD.getCurr g):ancs)) ts
     leaves ancs (DT.And ts _ g) = concatMap (leaves ((CPD.getCurr g):ancs)) ts
     leaves ancs (DT.Gen t _) = leaves ancs t
     leaves _ _ = []

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
