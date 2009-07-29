{-# LANGUAGE NoImplicitPrelude
           , GADTs
           , TypeOperators
           , FlexibleContexts
  #-}

-- | A data structure to reify combinatorial species.
module Math.Combinatorics.Species.AST
    (
      SpeciesTypedAST(..)
    , SpeciesAST(..)
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

-- | Reified combinatorial species.  Note that 'SpeciesTypedAST' has a
--   phantom type parameter which also reflects the structure, so we
--   can do case analysis on species at both the value and type level.
--
--   Of course, the non-uniform type parameter means that
--   'SpeciesTypedAST' cannot be an instance of the 'Species' class;
--   for that purpose the existential wrapper 'SpeciesAST' is
--   provided.
data SpeciesTypedAST s where
   O        :: SpeciesTypedAST Z
   I        :: SpeciesTypedAST (S Z)
   X        :: SpeciesTypedAST X
   E        :: SpeciesTypedAST E
   C        :: SpeciesTypedAST C
   Subset   :: SpeciesTypedAST Sub
   KSubset  :: Integer -> SpeciesTypedAST Sub
   Elt      :: SpeciesTypedAST Elt
   (:+:)    :: (ShowF (StructureF f), ShowF (StructureF g))
            => SpeciesTypedAST f -> SpeciesTypedAST g -> SpeciesTypedAST (f :+: g)
   (:*:)    :: (ShowF (StructureF f), ShowF (StructureF g))
            => SpeciesTypedAST f -> SpeciesTypedAST g -> SpeciesTypedAST (f :*: g)
   (:.:)    :: (ShowF (StructureF f), ShowF (StructureF g))
            => SpeciesTypedAST f -> SpeciesTypedAST g -> SpeciesTypedAST (f :.: g)
   (:><:)   :: (ShowF (StructureF f), ShowF (StructureF g))
            => SpeciesTypedAST f -> SpeciesTypedAST g -> SpeciesTypedAST (f :><: g)
   (:@:)   :: (ShowF (StructureF f), ShowF (StructureF g))
            => SpeciesTypedAST f -> SpeciesTypedAST g -> SpeciesTypedAST (f :@: g)
   Der      :: (ShowF (StructureF f))
            => SpeciesTypedAST f -> SpeciesTypedAST (Der f)
   OfSize   :: SpeciesTypedAST f -> (Integer -> Bool) -> SpeciesTypedAST f
   OfSizeExactly :: SpeciesTypedAST f -> Integer -> SpeciesTypedAST f
   NonEmpty :: SpeciesTypedAST f -> SpeciesTypedAST f

instance Show (SpeciesTypedAST s) where
  showsPrec _ O                   = showChar '0'
  showsPrec _ I                   = showChar '1'
  showsPrec _ X                   = showChar 'X'
  showsPrec _ E                   = showChar 'E'
  showsPrec _ C                   = showChar 'C'
  showsPrec _ Subset              = showChar 'p'
  showsPrec _ (KSubset n)         = showChar 'p' . shows n
  showsPrec _ (Elt)               = showChar 'e'
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
needsZT :: SpeciesTypedAST s -> Bool
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
  SA :: (ShowF (StructureF s), Typeable1 (StructureF s)) 
     => SpeciesTypedAST s -> SpeciesAST

-- | A version of 'needsZT' for 'SpeciesAST'.
needsZ :: SpeciesAST -> Bool
needsZ (SA s) = needsZT s

instance Show SpeciesAST where
  show (SA f) = show f

instance Additive.C SpeciesAST where
  zero   = SA O
  (SA f) + (SA g) = SA (f :+: g)
  negate = error "negation is not implemented yet!  wait until virtual species..."

instance Ring.C SpeciesAST where
  (SA f) * (SA g) = SA (f :*: g)
  one = SA I

instance Differential.C SpeciesAST where
  differentiate (SA f) = SA (Der f)

instance Species SpeciesAST where
  singleton               = SA X
  set                     = SA E
  cycle                   = SA C
  subset                  = SA Subset
  ksubset k               = SA (KSubset k)
  element                 = SA Elt
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

reify :: SpeciesAST -> SpeciesAST
reify = id

-- | Reflect an AST back into any instance of the 'Species' class.
reflectT :: Species s => SpeciesTypedAST f -> s
reflectT O                   = zero
reflectT I                   = one
reflectT X                   = singleton
reflectT E                   = set
reflectT C                   = cycle
reflectT Subset              = subset
reflectT (KSubset k)         = ksubset k
reflectT Elt                 = element
reflectT (f :+: g)           = reflectT f + reflectT g
reflectT (f :*: g)           = reflectT f * reflectT g
reflectT (f :.: g)           = reflectT f `o` reflectT g
reflectT (f :><: g)          = reflectT f >< reflectT g
reflectT (f :@: g)           = reflectT f @@ reflectT g
reflectT (Der f)             = oneHole (reflectT f)
reflectT (OfSize f p)        = ofSize (reflectT f) p
reflectT (OfSizeExactly f n) = ofSizeExactly (reflectT f) n
reflectT (NonEmpty f)        = nonEmpty (reflectT f)

-- | Reflect an AST back into any instance of the 'Species' class.
reflect :: Species s => SpeciesAST -> s
reflect (SA f) = reflectT f
