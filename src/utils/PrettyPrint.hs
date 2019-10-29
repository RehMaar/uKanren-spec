module PrettyPrint where

import Data.List (intercalate)

class PrettyPrint a where
    pretty :: a -> String

prettyList :: PrettyPrint a => [a] -> String
prettyList as = "[" ++ intercalate ", " (pretty <$> as) ++ "]"

-- instance (PrettyPrint a) => PrettyPrint [a] where
--     pretty as = "[" ++ intercalate ", " (pretty <$> as) ++ "]"
