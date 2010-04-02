{-# LANGUAGE NoImplicitPrelude
           , GeneralizedNewtypeDeriving
  #-}

-- | Some common types used by the species library, along with some
--   utility functions.
module Math.Combinatorics.Species.Types
    ( -- * Miscellaneous

      CycleType

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

-- | A representation of the cycle type of a permutation.  If @c ::
--   CycleType@ and @(k,n) `elem` c@, then the permutation has @n@
--   cycles of size @k@.
type CycleType = [(Integer, Integer)]

--------------------------------------------------------------------------------
--  Series types  --------------------------------------------------------------
--------------------------------------------------------------------------------

-- | Exponential generating functions, for counting labelled species.
newtype EGF = EGF { unEGF :: PS.T Rational }
  deriving (Additive.C, Differential.C, Ring.C, Show)

egfFromCoeffs :: [Rational] -> EGF
egfFromCoeffs = EGF . PS.fromCoeffs

liftEGF :: (PS.T Rational -> PS.T Rational) -> EGF -> EGF
liftEGF f (EGF x) = EGF (f x)

liftEGF2 :: (PS.T Rational -> PS.T Rational -> PS.T Rational)
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
