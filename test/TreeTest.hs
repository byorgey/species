{-# LANGUAGE NoImplicitPrelude,
             TemplateHaskell,
             TypeFamilies,
             DeriveDataTypeable,
             FlexibleInstances,
             UndecidableInstances #-}
import Math.Combinatorics.Species
import Math.Combinatorics.Species.Types
import Math.Combinatorics.Species.AST
import Math.Combinatorics.Species.AST.Instances

import Data.Typeable

import MyPrelude

data Tree2C = Tree2C
  deriving (Typeable, Show)

type instance Interp Tree2C self = Sum Unit (Prod self (Prod Id self))

data Tree2 a = Leaf2 | Node2 (Tree2 a) a (Tree2 a)
  deriving Show

instance ASTFunctor Tree2C where
  apply _ self = annI One :+: annI (annI self :*: annI (annI X :*: annI self))

instance Show a => Show (Mu Tree2C a) where
  show = show . unMu

instance Enumerable Tree2 where
  type StructTy Tree2 = Mu Tree2C
  iso (Mu (Inl _)) = Leaf2
  iso (Mu (Inr (Prod l (Prod (Id a) r)))) = Node2 (iso l) a (iso r)

tree2 :: Species s => s
tree2 = rec Tree2C

main = do
  print $ (enumerate tree2 [1,2] :: [Tree2 Int])
