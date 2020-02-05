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

{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

module OCanrenize where

import System.Process
import System.IO
import System.IO.Temp
import Data.Char
import Data.List (intercalate)
import Num
import Sort
import Syntax
import Driving
import Text.Printf

class OCanren a where
  ocanren :: a -> String

instance OCanren String where
  ocanren = id

instance OCanren v => OCanren (Term v) where
  ocanren (V v)        = ocanren v
  ocanren (C nil _) | map toLower nil == "nil"  = "nil ()"
  ocanren (C cons [h,t]) | map toLower cons == "cons" = printf "(%s %% %s)" (ocanren h) (ocanren t)
  ocanren (C "%"    [h,t]) = printf "(%s %% %s)" (ocanren h) (ocanren t)
  ocanren (C "O" []) = "zero"
  ocanren (C "S" [x]) = printf "succ (%s)" (ocanren x)
  ocanren (C "o" []) = "zero"
  ocanren (C "s" [x]) = printf "s (%s)" (ocanren x)
  ocanren (C "true" []) = printf "!!true"
  ocanren (C "false" []) = printf "!!false"
  ocanren (C "z" []) = "zero"
  ocanren (C "none" []) = "none ()"
  ocanren (C "ltrue" []) = "ltrue ()"
  ocanren (C "lfalse" []) = "lfalse ()"
  ocanren (C (f:o) ts) = printf "(%s)" $ (toLower f : o) ++ ' ' : printArgs (map ocanren ts)

instance OCanren v => OCanren (G v) where
  ocanren (t1 :=:  t2)  = printf "(%s === %s)" (ocanren t1) (ocanren t2)
  ocanren (g1 :/\: g2)  = printf "(%s &&& %s)" (ocanren g1) (ocanren g2)
  ocanren (g1 :\/: g2)  = printf "(%s ||| %s)" (ocanren g1) (ocanren g2)
  ocanren (Fresh x g )  = let (names, goal) = freshVars [x] g in printf "(fresh (%s) (%s))" (printArgs names) (ocanren goal)
  ocanren (Invoke f ts) = printf "(%s %s)" f (printArgs $ map ocanren ts)
  ocanren (Let (n, as, b) g) = printf "let rec %s %s = %s in %s" n (printArgs as) (ocanren b) (ocanren g)

-- printArgs [] = "()"
printArgs args = unwords $ map (\x -> if ' ' `elem` x then printf "(%s)" x else x ) args

ocanrenize :: String -> (G X, [String]) -> String
ocanrenize topLevelName (g, args) =
  printf "let %s %s = %s" topLevelName (printArgs args) (ocanren g)

ocanrenize' :: String -> (G X, [String], [Def]) -> String
ocanrenize' topLevelName (g, args, defs) = printf "let %s %s = %s %s" topLevelName (printArgs args) (printDefs defs) (ocanren g) where
  printFstDef (n, as, g) = printf "let rec %s %s = %s" n (printArgs as) (ocanren g)
  printLastDefs [] = "in "
  printLastDefs ((n, as, g) : ds) =
    printf "and %s %s = %s %s " n (printArgs as) (ocanren g) $ printLastDefs ds

  printDefs []     = ""
  printDefs (d:ds) = (printFstDef d) ++ " " ++ (printLastDefs ds)

toOCanren = toOCanren' ocanrenize

topLevel = toOCanren' ocanrenize'

toOCanren' printer filename topLevelName environment prog =
  do
    withSystemTempFile filename (\ tmp_name tmp ->
                                   do
                                     hPutStrLn tmp (printer topLevelName prog)
                                     hClose tmp
                                     printEnvironment filename environment
                                     system $ "cat " ++ tmp_name ++ " >> " ++ filename
                                     --system $ "camlp5o pr_o.cmo " ++ tmp_name ++ " >> " ++ filename
                                     system $ "ocamlformat " ++ filename ++ " -m 160 -i"
                                     return ()
                                )
  where
    printEnvironment filename (Just env) =
      do
        file <- openFile filename WriteMode
        hPutStrLn file env
        hClose file
    printEnvironment filename Nothing =
      do
        file <- openFile filename WriteMode
        hPutStrLn file "open GT"
        hPutStrLn file "open OCanren"
        hPutStrLn file "open Std"
        hPutStrLn file "open Nat"
        hPutStrLn file ""
        hClose file
