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

-}

module CPD.SldTreePrinter where

import DotPrinter
import qualified Eval as E
import Syntax
import CPD.LocalControl
import Text.Printf

instance DotPrinter SldTree where
  labelNode t@(Conj ch _ _) = addChild    t ch
  labelNode t@(Or ch _)     = addChildren t ch
  labelNode t               = addLeaf     t

instance Dot SldTree where
  dot (Leaf gs s _) = printf "Leaf <BR/> %s <BR/> %s" (dot (map getCurr gs)) (E.dotSigma s)
  dot Fail = "_|_"
  dot (Success s) = printf "S <BR/> %s" (E.dotSigma s)
  dot (Or _ _ ) = printf "O" -- <BR/> " ++ dot curr
  dot (Conj _ gs s)  = printf "C <BR/> %s <BR/> %s" (dot $ map getCurr gs) (E.dotSigma s) -- %s <BR/> %s" (show id') (dot curr)
