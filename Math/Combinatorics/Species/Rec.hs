{-# LANGUAGE DeriveDataTypeable
           , FlexibleInstances
           , TypeFamilies
  #-}

-- NOTE: this file is no longer part of the library; it's here only
-- for documentation/examples/hysterical raisins.

-- | Some common recursively defined species.
module Math.Combinatorics.Species.Rec
       (
         -- Binary trees
         BTreeC(..), BTree(..), bTree

       ) where

import NumericPrelude
import PreludeBase

import Data.Typeable

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Structures
import Math.Combinatorics.Species.AST
import Math.Combinatorics.Species.Enumerate

-- | Code for binary trees with data at internal nodes.
data BTreeC = BTreeC deriving Typeable

instance Show BTreeC where
  show _ = "BTree"

type instance Interp BTreeC self = Sum Unit (Prod Id (Prod self self))

instance ASTFunctor BTreeC where
  apply _ self = TOne :+: (TX :*: (self :*: self))

instance Show a => Show (Mu BTreeC a) where
  show = show . unMu

-- | Type of binary trees with data at internal nodes.
data BTree a = Empty | Node (BTree a) a (BTree a)
  deriving (Typeable, Eq, Read, Show)

instance Enumerable BTree where
  type StructTy BTree = Mu BTreeC
  iso (Mu (Inl _)) = Empty
  iso (Mu (Inr (Prod (Id a) (Prod l r)))) = Node (iso l) a (iso r)

bTree :: Species s => s
bTree = rec BTreeC

-- | Type of partitions.
data Partition a = Partition { getParts :: [[a]] }
  deriving (Typeable, Eq, Read, Show)
instance Enumerable Partition where
  type StructTy Partition = Comp Set Set
  iso (Comp ss) = Partition . map getSet . getSet $ ss