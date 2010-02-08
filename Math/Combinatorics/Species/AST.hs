{-# LANGUAGE NoImplicitPrelude
           , GADTs
           , TypeOperators
           , FlexibleContexts
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

    , reify
    , reflectT
    , reflect

    , List(..)
    , BTree(..)
    , HOFunctor(..)
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
   Rec      :: HOFunctor f => f -> SpeciesTypedAST (Mu f)

-- XXX just for testing
class HOFunctor f where
  unfold :: f -> SpeciesTypedAST g -> SpeciesTypedAST (Res f g)

data List = List deriving Typeable
type instance Res List self = Sum (Const Integer) (Prod Identity self)
instance HOFunctor List where
  unfold _ self = N 1 :+: (X :*: self)

instance Show a => Show (Mu List a) where
  show = show . unMu

data BTree = BTree deriving Typeable
type instance Res BTree self = Sum (Const Integer) (Prod Identity (Prod self self))
instance HOFunctor BTree where
  unfold _ self = N 1 :+: (X :*: (self :*: self))
instance Show a => Show (Mu BTree a) where
  show = show . unMu

instance Show (SpeciesTypedAST s) where
  showsPrec _ (N n)               = shows n
  showsPrec _ X                   = showChar 'X'
  showsPrec _ E                   = showChar 'E'
  showsPrec _ C                   = showChar 'C'
  showsPrec _ L                   = showChar 'L'
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
  SA :: (Typeable1 s)
     => SpeciesTypedAST s -> SpeciesAST

-- | A version of 'needsZT' for 'SpeciesAST'.
needsZ :: SpeciesAST -> Bool
needsZ (SA s) = needsZT s

instance Show SpeciesAST where
  show (SA f) = show f

instance Additive.C SpeciesAST where
  zero   = SA (N 0)
  (SA f) + (SA g) = SA (f :+: g)
  negate = error "negation is not implemented yet!  wait until virtual species..."

instance Ring.C SpeciesAST where
  (SA f) * (SA g) = SA (f :*: g)
  one = SA (N 1)
  fromInteger n = SA (N n)
  _ ^ 0 = one
  (SA f) ^ 1 = SA f
  (SA f) ^ n = case (SA f) ^ (n-1) of
                 (SA f') -> SA (f :*: f')

instance Differential.C SpeciesAST where
  differentiate (SA f) = SA (Der f)

instance Species SpeciesAST where
  singleton               = SA X
  set                     = SA E
  cycle                   = SA C
  list                    = SA L
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
-- > C . L+
-- > > reify (ksubset 3)
-- > E3 * E

reify :: SpeciesAST -> SpeciesAST
reify = id

-- | Reflect an AST back into any instance of the 'Species' class.
reflectT :: Species s => SpeciesTypedAST f -> s
reflectT (N n)               = fromInteger n
reflectT X                   = singleton
reflectT E                   = set
reflectT C                   = cycle
reflectT L                   = list
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
