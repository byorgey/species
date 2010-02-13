{-# LANGUAGE NoImplicitPrelude
           , GADTs
           , TypeFamilies
           , KindSignatures
           , DeriveDataTypeable
           , FlexibleInstances
  #-}

-- | A data structure to reify combinatorial species.
module Math.Combinatorics.Species.AST
    (
      SpeciesTypedAST(..)
    , SpeciesAST(..)
    , needsZT, needsZ

    , BTree(..)
    , ASTFunctor(..)
    ) where

import Math.Combinatorics.Species.Structures

import Data.Typeable

import NumericPrelude
import PreludeBase hiding (cycle)

-- | Reified combinatorial species.  Note that 'SpeciesTypedAST' has a
--   phantom type parameter which also reflects the structure, so we
--   can write quasi-dependently-typed functions over species, in
--   particular for species generation.
--
--   Of course, the non-uniform type parameter means that
--   'SpeciesTypedAST' cannot be an instance of the 'Species' class;
--   for that purpose the existential wrapper 'SpeciesAST' is
--   provided.
data SpeciesTypedAST (s :: * -> *) where
   N        :: Integer -> SpeciesTypedAST (Const Integer)
   X        :: SpeciesTypedAST Identity
   E        :: SpeciesTypedAST Set
   C        :: SpeciesTypedAST Cycle
   L        :: SpeciesTypedAST []
   Subset   :: SpeciesTypedAST Set
   KSubset  :: Integer -> SpeciesTypedAST Set
   Elt      :: SpeciesTypedAST Identity
   (:+:)    :: SpeciesTypedAST f -> SpeciesTypedAST g -> SpeciesTypedAST (Sum f g)
   (:*:)    :: SpeciesTypedAST f -> SpeciesTypedAST g -> SpeciesTypedAST (Prod f g)
   (:.:)    :: SpeciesTypedAST f -> SpeciesTypedAST g -> SpeciesTypedAST (Comp f g)
   (:><:)   :: SpeciesTypedAST f -> SpeciesTypedAST g -> SpeciesTypedAST (Prod f g)
   (:@:)    :: SpeciesTypedAST f -> SpeciesTypedAST g -> SpeciesTypedAST (Comp f g)
   Der      :: SpeciesTypedAST f -> SpeciesTypedAST (Comp f Star)
   OfSize   :: SpeciesTypedAST f -> (Integer -> Bool) -> SpeciesTypedAST f
   OfSizeExactly :: SpeciesTypedAST f -> Integer -> SpeciesTypedAST f
   NonEmpty :: SpeciesTypedAST f -> SpeciesTypedAST f
   Rec      :: ASTFunctor f => f -> SpeciesTypedAST (Mu f)

-- | Type class for codes which can be interpreted as higher-order
--   functors.
class ASTFunctor f where
  apply :: f -> SpeciesTypedAST g -> SpeciesTypedAST (Interp f g)

data BTree = BTree deriving Typeable
type instance Interp BTree self = Sum (Const Integer) (Prod Identity (Prod self self))
instance ASTFunctor BTree where
  apply _ self = N 1 :+: (X :*: (self :*: self))
instance Show a => Show (Mu BTree a) where
  show = show . unMu

-- | 'needsZT' is a predicate which checks whether a species uses any
--   of the operations which are not supported directly by ordinary
--   generating functions (composition, differentiation, cartesian
--   product, and functor composition), and hence need cycle index
--   series.
needsZT :: SpeciesTypedAST s -> Bool
needsZT L            = True
needsZT (f :+: g)    = needsZT f || needsZT g
needsZT (f :*: g)    = needsZT f || needsZT g
needsZT (_ :.: _)    = True
needsZT (_ :><: _)   = True
needsZT (_ :@: _)    = True
needsZT (Der _)      = True
needsZT (OfSize f _) = needsZT f
needsZT (OfSizeExactly f _) = needsZT f
needsZT (NonEmpty f) = needsZT f
needsZT _            = False

-- | An existential wrapper to hide the phantom type parameter to
--   'SpeciesTypedAST', so we can make it an instance of 'Species'.
data SpeciesAST where
  SA :: (Typeable1 s)
     => SpeciesTypedAST s -> SpeciesAST

-- | A version of 'needsZT' for 'SpeciesAST'.
needsZ :: SpeciesAST -> Bool
needsZ (SA s) = needsZT s

