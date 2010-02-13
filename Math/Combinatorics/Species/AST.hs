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
      SpeciesAST(..)
    , ESpeciesAST(..)
    , ASTFunctor(..)

    , needsZ, needsZE

    ) where

import Math.Combinatorics.Species.Structures

import Data.Typeable

import NumericPrelude
import PreludeBase hiding (cycle)

-- | Reified combinatorial species.  Note that 'SpeciesAST' has a
--   phantom type parameter which also reflects the structure, so we
--   can write quasi-dependently-typed functions over species, in
--   particular for species generation.
--
--   Of course, the non-uniform type parameter means that
--   'SpeciesAST' cannot be an instance of the 'Species' class;
--   for that purpose the existential wrapper 'ESpeciesAST' is
--   provided.
data SpeciesAST (s :: * -> *) where
   N        :: Integer -> SpeciesAST (Const Integer)
   X        :: SpeciesAST Identity
   E        :: SpeciesAST Set
   C        :: SpeciesAST Cycle
   L        :: SpeciesAST []
   Subset   :: SpeciesAST Set
   KSubset  :: Integer -> SpeciesAST Set
   Elt      :: SpeciesAST Identity
   (:+:)    :: SpeciesAST f -> SpeciesAST g -> SpeciesAST (Sum f g)
   (:*:)    :: SpeciesAST f -> SpeciesAST g -> SpeciesAST (Prod f g)
   (:.:)    :: SpeciesAST f -> SpeciesAST g -> SpeciesAST (Comp f g)
   (:><:)   :: SpeciesAST f -> SpeciesAST g -> SpeciesAST (Prod f g)
   (:@:)    :: SpeciesAST f -> SpeciesAST g -> SpeciesAST (Comp f g)
   Der      :: SpeciesAST f -> SpeciesAST (Comp f Star)
   OfSize   :: SpeciesAST f -> (Integer -> Bool) -> SpeciesAST f
   OfSizeExactly :: SpeciesAST f -> Integer -> SpeciesAST f
   NonEmpty :: SpeciesAST f -> SpeciesAST f
   Rec      :: ASTFunctor f => f -> SpeciesAST (Mu f)

-- | Type class for codes which can be interpreted as higher-order
--   functors.
class ASTFunctor f where
  apply :: f -> SpeciesAST g -> SpeciesAST (Interp f g)

-- | 'needsZ' is a predicate which checks whether a species uses any
--   of the operations which are not supported directly by ordinary
--   generating functions (composition, differentiation, cartesian
--   product, and functor composition), and hence need cycle index
--   series.
needsZ :: SpeciesAST s -> Bool
needsZ L            = True
needsZ (f :+: g)    = needsZ f || needsZ g
needsZ (f :*: g)    = needsZ f || needsZ g
needsZ (_ :.: _)    = True
needsZ (_ :><: _)   = True
needsZ (_ :@: _)    = True
needsZ (Der _)      = True
needsZ (OfSize f _) = needsZ f
needsZ (OfSizeExactly f _) = needsZ f
needsZ (NonEmpty f) = needsZ f
needsZ _            = False

-- | An existential wrapper to hide the phantom type parameter to
--   'SpeciesAST', so we can make it an instance of 'Species'.
data ESpeciesAST where
  SA :: (Typeable1 s)
     => SpeciesAST s -> ESpeciesAST

-- | A version of 'needsZ' for 'ESpeciesAST'.
needsZE :: ESpeciesAST -> Bool
needsZE (SA s) = needsZ s