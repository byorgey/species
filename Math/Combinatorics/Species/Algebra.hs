{-# LANGUAGE NoImplicitPrelude
           , GADTs
           , TypeOperators
           , FlexibleContexts
  #-}

-- | A data structure to reify combinatorial species.
module Math.Combinatorics.Species.Algebra 
    (
      SpeciesAlgT(..)
    , SpeciesAlg(..)
    , needsZT, needsZ

    , reify
    , reflectT
    , reflect
    
    ) where

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Types

import qualified Algebra.Additive as Additive
import qualified Algebra.Ring as Ring
import qualified Algebra.Differential as Differential

import Data.Typeable

import NumericPrelude
import PreludeBase hiding (cycle)

-- | Reified combinatorial species.  Note that 'SpeciesAlgT' has a
--   phantom type parameter which also reflects the structure, so we
--   can do case analysis on species at both the value and type level.
--
--   Of course, the non-uniform type parameter means that
--   'SpeciesAlgT' cannot be an instance of the 'Species' class; for
--   that purpose the existential wrapper 'SpeciesAlg' is provided.
data SpeciesAlgT s where
   O        :: SpeciesAlgT Z
   I        :: SpeciesAlgT (S Z)
   X        :: SpeciesAlgT X
   (:+:)    :: (ShowF (StructureF f), ShowF (StructureF g)) 
            => SpeciesAlgT f -> SpeciesAlgT g -> SpeciesAlgT (f :+: g)
   (:*:)    :: (ShowF (StructureF f), ShowF (StructureF g))
            => SpeciesAlgT f -> SpeciesAlgT g -> SpeciesAlgT (f :*: g)
   (:.:)    :: (ShowF (StructureF f), ShowF (StructureF g)) 
            => SpeciesAlgT f -> SpeciesAlgT g -> SpeciesAlgT (f :.: g)
   Der      :: (ShowF (StructureF f)) 
            => SpeciesAlgT f -> SpeciesAlgT (Der f)
   E        :: SpeciesAlgT E
   C        :: SpeciesAlgT C
   OfSize   :: SpeciesAlgT f -> (Integer -> Bool) -> SpeciesAlgT f
   OfSizeExactly :: SpeciesAlgT f -> Integer -> SpeciesAlgT f
   (:><:)   :: (ShowF (StructureF f), ShowF (StructureF g))
            => SpeciesAlgT f -> SpeciesAlgT g -> SpeciesAlgT (f :><: g)

-- XXX improve this
instance Show (SpeciesAlgT s) where
  show O = "0"
  show I = "1"
  show X = "X"
  show (f :+: g) = "(" ++ show f ++ " + " ++ show g ++ ")"
  show (f :*: g) = "(" ++ show f ++ " * " ++ show g ++ ")"
  show (f :.: g) = "(" ++ show f ++ " . " ++ show g ++ ")"
  show (Der f)   = show f ++ "'"
  show E         = "E"
  show C         = "C"
  show (OfSize f p) = "<" ++ show f ++ ">"
  show (OfSizeExactly f n) = show f ++ "_" ++ show n
  show (f :><: g) = "(" ++ show f ++ " >< " ++ show g ++ ")"

-- | 'needsZT' is a predicate which checks whether a species uses any
--   of the operations which are not supported directly by ordinary
--   generating functions (composition and differentiation), and hence
--   need cycle index series.
needsZT :: SpeciesAlgT s -> Bool
needsZT (f :+: g)    = needsZT f || needsZT g
needsZT (f :*: g)    = needsZT f || needsZT g
needsZT (_ :.: _)    = True
needsZT (_ :><: _)   = True
needsZT (Der _)      = True
needsZT (OfSize f _) = needsZT f
needsZT (OfSizeExactly f _) = needsZT f
needsZT _            = False

-- | An existential wrapper to hide the phantom type parameter to
--   'SpeciesAlgT', so we can make it an instance of 'Species'.
data SpeciesAlg where
  SA :: (ShowF (StructureF s), Typeable1 (StructureF s)) => SpeciesAlgT s -> SpeciesAlg

-- | A version of 'needsZT' for 'SpeciesAlg'.
needsZ :: SpeciesAlg -> Bool
needsZ (SA s) = needsZT s

instance Show SpeciesAlg where
  show (SA f) = show f

instance Additive.C SpeciesAlg where
  zero   = SA O
  (SA f) + (SA g) = SA (f :+: g)
  negate = error "negation is not implemented yet!  wait until virtual species..."

instance Ring.C SpeciesAlg where
  (SA f) * (SA g) = SA (f :*: g)
  one = SA I

instance Differential.C SpeciesAlg where
  differentiate (SA f) = SA (Der f)

instance Species SpeciesAlg where
  singleton               = SA X
  set                     = SA E
  cycle                   = SA C
  o (SA f) (SA g)         = SA (f :.: g)
  ofSize (SA f) p         = SA (OfSize f p)
  ofSizeExactly (SA f) n  = SA (OfSizeExactly f n)
  cartesian (SA f) (SA g) = SA (f :><: g)

-- | Reify a species expression into a tree.  Of course, this is just
--   the identity function with a usefully restricted type.  For example:
--
-- > > reify octopus
-- > (C . C'_+)
reify :: SpeciesAlg -> SpeciesAlg
reify = id

-- | Reflect a species back into any instance of the 'Species' class.
reflectT :: Species s => SpeciesAlgT f -> s
reflectT O = zero
reflectT I = one
reflectT X = singleton
reflectT (f :+: g) = reflectT f + reflectT g
reflectT (f :*: g) = reflectT f * reflectT g
reflectT (f :.: g) = reflectT f `o` reflectT g
reflectT (Der f)   = oneHole (reflectT f)
reflectT E = set
reflectT C = cycle
reflectT (OfSize f p) = ofSize (reflectT f) p
reflectT (OfSizeExactly f n) = ofSizeExactly (reflectT f) n
reflectT (f :><: g) = cartesian (reflectT f) (reflectT g)

-- | A version of 'reflectT' for the existential wrapper 'SpeciesAlg'.
reflect :: Species s => SpeciesAlg -> s
reflect (SA f) = reflectT f
