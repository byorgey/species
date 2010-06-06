{-# LANGUAGE NoImplicitPrelude
  #-}
-- | A simple implementation of intervals of natural numbers, for use
--   in tracking the possible sizes of structures of a species.  For
--   example, the species X + X^2 + X^3 will correspond to the
--   interval [1,3].
module Math.Combinatorics.Species.Util.Interval
    ( NatO(..)
    , Interval(..), allNats
    , decrI, union, intersect, elem
    ) where

import NumericPrelude
import PreludeBase hiding (elem)

import qualified Algebra.Additive as Additive
import qualified Algebra.Ring as Ring

data NatO = Nat Integer | Omega
  deriving (Eq, Ord, Show)

decr :: NatO -> NatO
decr (Nat 0) = Nat 0
decr (Nat n) = Nat (n-1)
decr Omega   = Omega

instance Additive.C NatO where
  zero          = Nat 0
  Nat m + Nat n = Nat (m + n)
  _ + _         = Omega
  negate = error "naturals with omega only form a semiring"

instance Ring.C NatO where
  one = Nat 1
  Nat 0 * _     = Nat 0
  Nat m * Nat n = Nat (m * n)
  _ * _         = Omega

  fromInteger = Nat

data Interval = I { iLow  :: Integer
                  , iHigh :: NatO
                  }

allNats :: Interval
allNats = I 0 Omega

decrI :: Interval -> Interval
decrI (I 0 h) = I 0 (decr h)
decrI (I l h) = I (l-1) (decr h)

union :: Interval -> Interval -> Interval
union (I l1 h1) (I l2 h2) = I (min l1 l2) (max h1 h2)

intersect :: Interval -> Interval -> Interval
intersect (I l1 h1) (I l2 h2) = I (max l1 l2) (min h1 h2)

instance Additive.C Interval where
  zero = I 0 0
  (I l1 h1) + (I l2 h2) = I (l1 + l2) (h1 + h2)
  negate = error "Interval negation: intervals only form a semiring"

instance Ring.C Interval where
  one = I 1 1
  (I l1 h1) * (I l2 h2) = I (l1 * l2) (h1 * h2)
  fromInteger n = I n (Nat n)

elem :: Integer -> Interval -> Bool
elem n (I lo Omega)    = lo <= n
elem n (I lo (Nat hi)) = lo <= n && n <= hi
