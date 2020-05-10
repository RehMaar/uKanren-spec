module Embedding where

import Syntax
import Utils

import Data.List (sort)
import Data.Maybe (isJust)
import Data.Foldable (foldl')

import qualified Data.Map.Strict as Map

infixl 6 <|

class AlwaysEmbeddable a => Homeo a where
  couple :: a -> a -> Bool
  diving :: a -> a -> Bool
  homeo  :: a -> a -> Bool
  homeo x y = couple x y || diving x y

  (<|) :: a -> a -> Bool
  (<|) = homeo

instance Homeo (Term a) where
  couple (C n as) (C m bs) | n == m && length as == length bs =
    all (uncurry homeo) $ zip as bs
  couple _ _ = False

  diving v (C _ as) = any (homeo v) as
  diving _ _ = False

  homeo (V _) (V _) = True
  homeo x y = couple x y || diving x y

instance Homeo (G a) where
  couple goal@(Invoke f as) (Invoke g bs)
    | isAlwaysEmbeddable goal || f == g && length as == length bs
    = all (uncurry homeo) $ zip as bs
  couple _ _ = False

  diving _ _ = False

instance Homeo [G a] where
  couple = error "Coupling isn't defined for a list of goals"
  diving = error "Diving isn't defined for a list of goals"

  homeo gs hs =
    any (all (uncurry homeo) . zip gs) (subconjs hs (length gs))

class (Eq b) => Instance a b | b -> a where
  inst :: b -> b -> Map.Map a (Term a) -> Maybe (Map.Map a (Term a))

  -- |e2 is an **instance** of e1, if exists a substitution O
  -- such as e1 O = e2.
  -- e1 `inst` e2 = O => substitute O e1 = e2
  isInst :: b -> b -> Bool
  isInst x y = isJust $ inst x y Map.empty

  isStrictInst :: b -> b -> Bool
  isStrictInst x y = isInst x y && not (isInst y x)

  isVariant :: b -> b -> Bool
  isVariant x y = x == y || isInst x y && isInst y x

  isRenaming :: b -> b -> Bool
  isRenaming x y =
    x == y || maybe False (all (\e -> case e of V _ -> True; _ -> False) . Map.elems) (inst x y Map.empty)

  instanceCheck :: Foldable t => b -> t b -> Bool
  instanceCheck g = any (`isInst` g)

  variantCheck :: Foldable t => b -> t b -> Bool
  variantCheck g = any (isVariant g)

instance (Eq a, Ord a) => Instance a (Term a) where
  inst (V v) u subst =
    case Map.lookup v subst of
      Just w | u == w -> Just subst
      Just w -> Nothing
      Nothing -> Just $ Map.insert v u subst
  inst (C n as) (C m bs) subst
    | n == m,
      length as == length bs =
      foldl' (\s (a, b) -> s >>= \s -> inst a b s) (Just subst) (zip as bs)
  inst _ _ _ = Nothing

instance (Eq a, Ord a) => Instance a (G a) where
  inst (Invoke f as) (Invoke g bs) subst
    | f == g
    , length as == length bs =
      foldl' (\s (a, b) -> s >>= \s -> inst a b s) (Just subst) (zip as bs)
  inst _ _ _ = Nothing


instance (Eq a, Ord a) => Instance a [G a] where
  inst as bs subst
    | length as == length bs
    = foldl' (\s (a, b) -> s >>= \s -> inst a b s) (Just subst) $ zip as bs
  inst _ _ _ = Nothing


class AlwaysEmbeddable a where
  isAlwaysEmbeddable :: a -> Bool

instance AlwaysEmbeddable (G a) where
  isAlwaysEmbeddable (Invoke f _) = f `elem` []
  isAlwaysEmbeddable _ = False

instance AlwaysEmbeddable [G a] where
  isAlwaysEmbeddable = null

instance AlwaysEmbeddable (Term a) where
  isAlwaysEmbeddable = const True

-- Strict homeomorphic embedding. Explore: use a variants check instead of the instance check.
class (Homeo b, Instance a b, Eq b) => Embed a b | b -> a where
  embed :: b -> b -> Bool
  embed g h = isAlwaysEmbeddable g || g == h || homeo g h && not (isStrictInst h g)

instance (Ord a, Eq a) => Embed a (G a)
instance (Ord a, Eq a) => Embed a [G a] where
  embed gs hs = any (and . zipWith embed gs) $ subconjs hs (length gs)
