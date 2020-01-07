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
  let (l, p) = DT.countLeafs t
  let n = DT.countNodes t
  putStrLn $ "Depth: " ++ show d ++ " Leafs: " ++ show l ++  " (Pruned: " ++ show p ++ ")" ++ " Nodes: " ++ show n

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
