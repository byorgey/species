{-# LANGUAGE NoImplicitPrelude,
             TemplateHaskell,
             TypeFamilies,
             DeriveDataTypeable,
             FlexibleInstances,
             UndecidableInstances #-}
import Math.Combinatorics.Species.TH
import Math.Combinatorics.Species

import MyPrelude

data Florp a = Fleep [a] a
  deriving Show

data Foo a = Baz | Bar a (Foo a)
  deriving Show

$(deriveSpecies ''Florp)
$(deriveSpecies ''Foo)

data Tree a = Leaf | Node a (Tree a) (Tree a)
  deriving Show

$(deriveSpecies ''Tree)

data Tree2 a = Leaf2 | Node2 (Tree2 a) a (Tree2 a)
  deriving Show

$(deriveSpecies ''Tree2)

main = do
  print $ (enumerate tree [1,2] :: [Tree Int])
  print $ (enumerate tree2 [1,2] :: [Tree2 Int])
