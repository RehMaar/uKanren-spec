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

module Utils where
    
import Data.List

fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

snd3 :: (a, b, c) -> b
snd3 (_, x, _) = x

trd3 :: (a, b, c) -> c
trd3 (_, _, x) = x

snd4 :: (a, b, c, d) -> b
snd4 (_, x, _, _) = x

trd4 :: (a, b, c, d) -> c
trd4 (_, _, x, _) = x

lst4 :: (a, b, c, d) -> d
lst4 (_, _, _, x) = x

generateSplits :: Eq a => [a] -> Int -> [([a], [a])]
generateSplits xs n =
  let sub = filter (\x -> n == length x) $ subsequences xs in
  [ (x, xs \\ x) | x <- sub ]

subconjs :: [a] -> Int -> [[a]]
subconjs gs n = combinations n gs
  where
    combinations :: Int -> [a] -> [[a]]
    combinations 0 _ = [[]]
    combinations _ [] = []
    combinations n (x:xs) = (map (x:) (combinations (n-1) xs)) ++ (combinations n xs)

zipBy :: Eq a => (b -> a) -> [b] -> [b] -> [(b, b)]
zipBy f b1 b2 = zipBy' f f b1 b2
  where
    zipBy' :: Eq a => (b -> a) -> (c -> a) -> [b] -> [c] -> [(b, c)]
    zipBy' f g bs cs = filter (\(b, c) -> f b == g c) $ (,) <$> bs <*> cs
