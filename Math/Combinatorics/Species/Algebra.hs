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
   E        :: SpeciesAlgT E
   C        :: SpeciesAlgT C
   (:+:)    :: (ShowF (StructureF f), ShowF (StructureF g)) 
            => SpeciesAlgT f -> SpeciesAlgT g -> SpeciesAlgT (f :+: g)
   (:*:)    :: (ShowF (StructureF f), ShowF (StructureF g))
            => SpeciesAlgT f -> SpeciesAlgT g -> SpeciesAlgT (f :*: g)
   (:.:)    :: (ShowF (StructureF f), ShowF (StructureF g)) 
            => SpeciesAlgT f -> SpeciesAlgT g -> SpeciesAlgT (f :.: g)
   (:><:)   :: (ShowF (StructureF f), ShowF (StructureF g))
            => SpeciesAlgT f -> SpeciesAlgT g -> SpeciesAlgT (f :><: g)
   (:@:)   :: (ShowF (StructureF f), ShowF (StructureF g))
            => SpeciesAlgT f -> SpeciesAlgT g -> SpeciesAlgT (f :@: g)
   Der      :: (ShowF (StructureF f)) 
            => SpeciesAlgT f -> SpeciesAlgT (Der f)
   OfSize   :: SpeciesAlgT f -> (Integer -> Bool) -> SpeciesAlgT f
   OfSizeExactly :: SpeciesAlgT f -> Integer -> SpeciesAlgT f
   NonEmpty :: SpeciesAlgT f -> SpeciesAlgT f

instance Show (SpeciesAlgT s) where
  showsPrec _ O                   = showChar '0'
  showsPrec _ I                   = showChar '1'
  showsPrec _ X                   = showChar 'X'
  showsPrec _ E                   = showChar 'E'
  showsPrec _ C                   = showChar 'C'
  showsPrec p (f :+: g)           = showParen (p>6)  $ showsPrec 6 f . showString " + "  . showsPrec 6 g
  showsPrec p (f :*: g)           = showParen (p>=7) $ showsPrec 7 f . showString " * "  . showsPrec 7 g
  showsPrec p (f :.: g)           = showParen (p>=7) $ showsPrec 7 f . showString " . "  . showsPrec 7 g
  showsPrec p (f :><: g)          = showParen (p>=7) $ showsPrec 7 f . showString " >< " . showsPrec 7 g
  showsPrec p (f :@: g)           = showParen (p>=7) $ showsPrec 7 f . showString " @ "  . showsPrec 7 g
  showsPrec p (Der f)             = showsPrec 11 f . showChar '\''
  showsPrec _ (OfSize f p)        = showChar '<' .  showsPrec 0 f . showChar '>'
  showsPrec _ (OfSizeExactly f n) = showsPrec 11 f . shows n
  showsPrec _ (NonEmpty f)        = showsPrec 11 f . showChar '+'

-- | 'needsZT' is a predicate which checks whether a species uses any
--   of the operations which are not supported directly by ordinary
--   generating functions (composition, differentiation, cartesian
--   product, and functor composition), and hence need cycle index
--   series.
needsZT :: SpeciesAlgT s -> Bool
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
  cartesian (SA f) (SA g) = SA (f :><: g)
  fcomp (SA f) (SA g)     = SA (f :@: g)
  ofSize (SA f) p         = SA (OfSize f p)
  ofSizeExactly (SA f) n  = SA (OfSizeExactly f n)
  nonEmpty (SA f)         = SA (NonEmpty f)

-- | Reify a species expression into an AST.  Of course, this is just
--   the identity function with a usefully restricted type.  For
--   example:
--
-- > > reify octopus
-- > C . C'+
-- > > reify (ksubset 3)
-- > E3 * E

reify :: SpeciesAlg -> SpeciesAlg
reify = id

-- | Reflect an AST back into any instance of the 'Species' class.
reflectT :: Species s => SpeciesAlgT f -> s
reflectT O                   = zero
reflectT I                   = one
reflectT X                   = singleton
reflectT E                   = set
reflectT C                   = cycle
reflectT (f :+: g)           = reflectT f + reflectT g
reflectT (f :*: g)           = reflectT f * reflectT g
reflectT (f :.: g)           = reflectT f `o` reflectT g
reflectT (f :><: g)          = reflectT f >< reflectT g
reflectT (f :@: g)           = reflectT f @@ reflectT g
reflectT (Der f)             = oneHole (reflectT f)
reflectT (OfSize f p)        = ofSize (reflectT f) p
reflectT (OfSizeExactly f n) = ofSizeExactly (reflectT f) n
reflectT (NonEmpty f)        = nonEmpty (reflectT f)

-- | A version of 'reflectT' for the existential wrapper 'SpeciesAlg'.
reflect :: Species s => SpeciesAlg -> s
reflect (SA f) = reflectT f
