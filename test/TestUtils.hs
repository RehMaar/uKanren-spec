module TestUtils where

import System.Process (system)
import System.Exit (ExitCode)
import Data.Maybe
import Text.Printf

import Syntax
import DotPrinter
import SldTreePrinter
import GlobalTreePrinter
import Utils

import qualified CPD
import qualified CpdResidualization as CR
import qualified GlobalControl as GC
import qualified Purification as P
import qualified OCanrenize as OC
import qualified Embedding as Emb

import qualified Unfold.SeqUnfold as SU
import qualified Unfold.FullUnfold as FU
import qualified Unfold.RandUnfold as RU
import qualified Unfold.NonRecUnfold as NU
import qualified Unfold.RecUnfold as RecU
import qualified Unfold.MaxUnfold as MaxU
import qualified Unfold.MinUnfold as MinU
import qualified Unfold.Unfold as U

import qualified DTree as DT
import qualified DTResidualize as DTR

import qualified LogicInt as LI
import qualified List as L

import Data.Monoid

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

ocanren specMethod filename goal = do
  let p = pur goal
  let name = filename ++ ".ml"
  OC.topLevel name "topLevelSU" Nothing p
  where
    pur goal = let
        (tree, logicGoal, names) = specMethod goal
        f = DTR.topLevel tree
        (goal', names', defs) = P.purification (f, vident <$> reverse names)
      in (goal', names', (\(n1, n2, n3) -> (n1, n2, fromJust $ DTR.simplify n3)) <$> defs)

ocanrenId specMethod filename goal = do
  let p = pur goal
  let name = filename ++ ".ml"
  OC.topLevel name "topLevelSU" Nothing p
  where
    pur goal = let
        (tree, logicGoal, names) = specMethod goal
        f = DTR.topLevel tree
        (goal', names', defs) = P.identity (f, vident <$> reverse names)
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
    (tree, logicGoal, names) = SU.topLevel goal
    f = DTR.topLevel tree
    (goal', names', defs) = P.purification (f, vident <$> reverse names)
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
        (tree, logicGoal, names) = SU.topLevel goal
        f = DTR.topLevel tree
        (goal', names', defs) = P.purification (f, vident <$> reverse names)
      in (goal', names', (\(n1, n2, n3) -> (n1, n2, fromJust $ DTR.simplify n3)) <$> defs)

--
-- Tree statistic
--
statTree :: DT.DTree -> IO ()
statTree t = do
  let d = DT.countDepth t
  let (l, s, f) = DT.countLeafs t
  let n = DT.countNodes t
  putStrLn $ "Depth: " ++ show d ++ " Leafs: " ++ show l ++  " Success: " ++ show s ++ " Fail: " ++ show f ++ " Nodes: " ++ show n

statMTree :: DTR.MarkedTree -> IO ()
statMTree t = do
  let d = DTR.countDepth t
  let (l, f, s) = DTR.countLeafs t
  let (n, fn) = DTR.countNodes t
  putStrLn $ "Depth: " ++ show d ++ " Leafs: " ++ show l ++ " Fail: " ++ show f ++ " Success: " ++ show s ++ " Nodes: " ++ show n ++ " FunCallNodes: " ++ show fn

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

statMethod goal name topLevel = do
  putStr $ name ++ ": "
  statTree $ fst3 $ topLevel goal

statMethods goal = do
  -- statMethod goal "FU  " FU.topLevel
  statMethod goal "SU  " SU.topLevel
  statMethod goal "RU  " (RU.topLevel 17)
  statMethod goal "NU  " NU.topLevel
  statMethod goal "RecU" RecU.topLevel
  statMethod goal "MinU  " MinU.topLevel
  statMethod goal "MaxU  " MaxU.topLevel

statRandIO goal = do
  (t, g, ns) <- RU.topLevelIO goal
  statTree t

statMMethods goal = do
  -- statMMethod goal "FU  " FU.topLevel
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
