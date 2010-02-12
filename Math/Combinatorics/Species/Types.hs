{-# LANGUAGE NoImplicitPrelude
           , GeneralizedNewtypeDeriving
  #-}

-- | Some common types used by the species library, along with some
--   utility functions.
module Math.Combinatorics.Species.Types
    ( -- * Miscellaneous

      CycleType

      -- * Lazy multiplication

    , LazyRing(..)
    , LazyQ
    , LazyZ

      -- * Series types

    , EGF(..)
    , egfFromCoeffs
    , liftEGF
    , liftEGF2

    , GF(..)
    , gfFromCoeffs
    , liftGF
    , liftGF2

    , CycleIndex(..)
    , ciFromMonomials
    , liftCI
    , liftCI2

    , filterCoeffs
    , selectIndex

    ) where

import NumericPrelude
import PreludeBase
import Data.List (genericReplicate)


import qualified MathObj.PowerSeries as PS
import qualified MathObj.MultiVarPolynomial as MVP
import qualified MathObj.Monomial as Monomial

import qualified Algebra.Additive as Additive
import qualified Algebra.Ring as Ring
import qualified Algebra.Differential as Differential
import qualified Algebra.ZeroTestable as ZeroTestable
import qualified Algebra.Field as Field

import Data.Lub (parCommute, HasLub(..), flatLub)

-- | A representation of the cycle type of a permutation.  If @c ::
--   CycleType@ and @(k,n) `elem` c@, then the permutation has @n@
--   cycles of size @k@.
type CycleType = [(Integer, Integer)]

--------------------------------------------------------------------------------
--  Lazy multiplication  -------------------------------------------------------
--------------------------------------------------------------------------------

-- | If @T@ is an instance of @Ring@, then @LazyRing T@ is isomorphic
--   to T but with a lazy multiplication: @0 * undefined = undefined * 0
--   = 0@, and @1 * a = a * 1 = a@.
newtype LazyRing a = LR { unLR :: a }
  deriving (Eq, Ord, Additive.C, ZeroTestable.C, Field.C)

instance HasLub (LazyRing a) where
  lub = flatLub

instance Show a => Show (LazyRing a) where
  show (LR r) = show r

instance (Eq a, Ring.C a) => Ring.C (LazyRing a) where
  (*) = parCommute lazyTimes
    where lazyTimes (LR 0) _ = LR 0
          lazyTimes (LR 1) x = x
          lazyTimes (LR a) (LR b) = LR (a*b)
  fromInteger = LR . fromInteger

type LazyQ = LazyRing Rational
type LazyZ = LazyRing Integer

--------------------------------------------------------------------------------
--  Series types  --------------------------------------------------------------
--------------------------------------------------------------------------------

-- | Exponential generating functions, for counting labelled species.
newtype EGF = EGF (PS.T LazyQ)
  deriving (Additive.C, Ring.C, Differential.C, Show)

egfFromCoeffs :: [LazyQ] -> EGF
egfFromCoeffs = EGF . PS.fromCoeffs

liftEGF :: (PS.T LazyQ -> PS.T LazyQ) -> EGF -> EGF
liftEGF f (EGF x) = EGF (f x)

liftEGF2 :: (PS.T LazyQ -> PS.T LazyQ -> PS.T LazyQ)
         -> EGF -> EGF -> EGF
liftEGF2 f (EGF x) (EGF y) = EGF (f x y)

-- | Ordinary generating functions, for counting unlabelled species.
newtype GF = GF (PS.T Integer)
  deriving (Additive.C, Ring.C, Show)

gfFromCoeffs :: [Integer] -> GF
gfFromCoeffs = GF . PS.fromCoeffs

liftGF :: (PS.T Integer -> PS.T Integer) -> GF -> GF
liftGF f (GF x) = GF (f x)

liftGF2 :: (PS.T Integer -> PS.T Integer -> PS.T Integer)
         -> GF -> GF -> GF
liftGF2 f (GF x) (GF y) = GF (f x y)

-- | Cycle index series.
newtype CycleIndex = CI (MVP.T Rational)
  deriving (Additive.C, Ring.C, Differential.C, Show)

ciFromMonomials :: [Monomial.T Rational] -> CycleIndex
ciFromMonomials = CI . MVP.Cons

liftCI :: (MVP.T Rational -> MVP.T Rational)
        -> CycleIndex -> CycleIndex
liftCI f (CI x) = CI (f x)

liftCI2 :: (MVP.T Rational -> MVP.T Rational -> MVP.T Rational)
        -> CycleIndex -> CycleIndex -> CycleIndex
liftCI2 f (CI x) (CI y) = CI (f x y)

-- Some series utility functions

-- | Filter the coefficients of a series according to a predicate.
filterCoeffs :: (Additive.C a) => (Integer -> Bool) -> [a] -> [a]
filterCoeffs p = zipWith (filterCoeff p) [0..]
    where filterCoeff p n x | p n       = x
                            | otherwise = Additive.zero

-- | Set every coefficient of a series to 0 except the selected
--   index. Truncate any trailing zeroes.
selectIndex :: (Ring.C a, Eq a) => Integer -> [a] -> [a]
selectIndex n xs = xs'
    where mx = safeIndex n xs
          safeIndex _ []     = Nothing
          safeIndex 0 (x:_)  = Just x
          safeIndex n (_:xs) = safeIndex (n-1) xs
          xs' = case mx of
                  Just 0 -> []
                  Just x -> genericReplicate n 0 ++ [x]
                  _      -> []
