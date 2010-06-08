{-# LANGUAGE NoImplicitPrelude
  #-}
-- | A simple implementation of intervals of natural numbers, for use
--   in tracking the possible sizes of structures of a species.  For
--   example, the species X + X^2 + X^3 will correspond to the
--   interval [1,3].
module Math.Combinatorics.Species.Util.Interval
    (
    -- * The 'NatO' type
      NatO, omega, natO

    -- * The 'Interval' type
    , Interval, iLow, iHigh

    -- * Interval operations
    , decrI, union, intersect, elem, toList

    -- * Constructing intervals
    , natsI, fromI, emptyI, omegaI
    ) where

import NumericPrelude
import PreludeBase hiding (elem)

import qualified Algebra.Additive as Additive
import qualified Algebra.Ring as Ring

-- | 'NatO' is an explicit representation of the co-inductive Nat type
--   which admits an infinite value, omega.  Our intuition for the
--   semantics of 'NatO' comes from thinking of it as an efficient
--   representation of lazy unary natural numbers, except that we can
--   actually test for omega in finite time.
data NatO = Nat Integer | Omega
  deriving (Eq, Ord, Show)

omega :: NatO
omega = Omega

-- | Eliminator for 'NatO' values.
natO :: (Integer -> a) -> a -> NatO -> a
natO _ o Omega = o
natO f _ (Nat n) = f n

-- | Decrement a possibly infinite natural. Zero and omega are both
--   fixed points of 'decr'.
decr :: NatO -> NatO
decr (Nat 0) = Nat 0
decr (Nat n) = Nat (n-1)
decr Omega   = Omega

-- | 'NatO' forms an additive monoid, with zero as the identity.  This
--   doesn't quite fit since Additive.C is supposed to be for groups,
--   so the 'negate' method just throws an error.  But we'll never use
--   it and 'NatO' won't be directly exposed to users of the species
--   library anyway.
instance Additive.C NatO where
  zero          = Nat 0
  Nat m + Nat n = Nat (m + n)
  _ + _         = Omega
  negate = error "naturals with omega only form a semiring"

-- | In fact, 'NatO' forms a semiring, with 1 as the multiplicative
--   unit.
instance Ring.C NatO where
  one = Nat 1
  Nat 0 * _     = Nat 0
  _ * Nat 0     = Nat 0
  Nat m * Nat n = Nat (m * n)
  _ * _         = Omega

  fromInteger = Nat

-- | An 'Interval' is a closed range of consecutive integers.  Both
--   endpoints are represented as 'NatO' values.  For example, [2,5]
--   represents the values 2,3,4,5; [2,omega] represents all integers
--   greater than 1; intervals where the first endpoint is greater than the
--   second also represent the empty interval.
data Interval = I { iLow  :: NatO
                  , iHigh :: NatO
                  }
  deriving Show

-- | Decrement both endpoints of an interval.
decrI :: Interval -> Interval
decrI (I l h) = I (decr l) (decr h)

-- | The union of two intervals is the smallest interval containing
--   both.
union :: Interval -> Interval -> Interval
union (I l1 h1) (I l2 h2) = I (min l1 l2) (max h1 h2)

-- | The intersection of two intervals is the largest interval
--   contained in both.
intersect :: Interval -> Interval -> Interval
intersect (I l1 h1) (I l2 h2) = I (max l1 l2) (min h1 h2)

-- | Intervals can be added by adding their endpoints pointwise.
instance Additive.C Interval where
  zero = I 0 0
  (I l1 h1) + (I l2 h2) = I (l1 + l2) (h1 + h2)
  negate = error "Interval negation: intervals only form a semiring"

-- | Intervals form a semiring, with the multiplication operation
--   being pointwise multiplication of their endpoints.
instance Ring.C Interval where
  one = I 1 1
  (I l1 h1) * (I l2 h2) = I (l1 * l2) (h1 * h2)
  fromInteger n = I (Nat n) (Nat n)

-- | Test a given integer for interval membership.
elem :: Integer -> Interval -> Bool
elem n (I lo Omega)    = lo <= fromInteger n
elem n (I lo (Nat hi)) = lo <= fromInteger n && n <= hi

-- | Convert an interval to a list of Integers.
toList :: Interval -> [Integer]
toList (I Omega Omega) = []
toList (I lo hi) | lo > hi = []
toList (I (Nat lo) Omega) = [lo..]
toList (I (Nat lo) (Nat hi)) = [lo..hi]

-- | The range [0,omega] containing all natural numbers.
natsI :: Interval
natsI = I 0 Omega

-- | Construct an open range [n,omega].
fromI :: NatO -> Interval
fromI n = I n Omega

-- | The empty interval.
emptyI :: Interval
emptyI = I 1 0

-- | The interval which contains only omega.
omegaI :: Interval
omegaI = I Omega Omega