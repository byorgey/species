{-# LANGUAGE NoImplicitPrelude,
             TemplateHaskell,
             TypeFamilies,
             DeriveDataTypeable,
             FlexibleInstances,
             UndecidableInstances #-}
import Math.Combinatorics.Species.TH
import Math.Combinatorics.Species

import NumericPrelude

-- data Florp a = Fleep [a] a
--   deriving Show

data Foo a = Baz | Bar a (Foo a)
  deriving Show

-- $(deriveDefaultSpecies ''Florp)
$(deriveDefaultSpecies ''Foo)

data Tree a = Leaf | Node a (Tree a) (Tree a)
  deriving Show

$(deriveDefaultSpecies ''Tree)

data Tree2 a = Leaf2 | Node2 (Tree2 a) a (Tree2 a)
  deriving Show

$(deriveDefaultSpecies ''Tree2)

data Parens a = LeafP a | NodeP (Parens a) (Parens a)

instance Show (Parens a) where
  show (LeafP _) = "."
  show (NodeP p1 p2) = "(" ++ show p1 ++ show p2 ++ ")"

$(deriveDefaultSpecies ''Parens)

main = do
  print $ (enumerate tree [1,2] :: [Tree Int])
  print $ (enumerate tree2 [1,2] :: [Tree2 Int])
