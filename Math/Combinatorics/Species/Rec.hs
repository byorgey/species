{-# LANGUAGE DeriveDataTypeable
           , FlexibleInstances
           , TypeFamilies
  #-}

-- | Some common recursively defined species.
module Math.Combinatorics.Species.Rec
       (
         -- Binary trees
         BTreeC(..), BTree(..)

       ) where

import NumericPrelude
import PreludeBase

import Data.Typeable

import Math.Combinatorics.Species.Structures
import Math.Combinatorics.Species.AST
import Math.Combinatorics.Species.Generate

-- | Code for binary trees with data at internal nodes.
data BTreeC = BTreeC deriving Typeable

type instance Interp BTreeC self = Sum (Const Integer) (Prod Identity (Prod self self))

instance ASTFunctor BTreeC where
  apply _ self = N 1 :+: (X :*: (self :*: self))

instance Show a => Show (Mu BTreeC a) where
  show = show . unMu

-- | Type of binary trees with data at internal nodes.
data BTree a = Empty | Node (BTree a) a (BTree a)
  deriving (Typeable)

instance Show a => Show (BTree a) where
  show Empty = ""
  show (Node l a r) = "(" ++ show l ++ show a ++ show r ++ ")"

instance Iso BTree where
  type SType BTree = Mu BTreeC
  iso (Mu (Sum (Left _))) = Empty
  iso (Mu (Sum (Right (Prod (Identity a, Prod (l, r)))))) = Node (iso l) a (iso r)
