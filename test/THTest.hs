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

$(deriveEnumerable ''Florp)
$(deriveEnumerable ''Foo)

data Tree a = Leaf | Node a (Tree a) (Tree a)
  deriving Show

$(deriveEnumerable ''Tree)

main = print "hay!"
