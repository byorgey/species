{-# LANGUAGE NoImplicitPrelude #-}
module Math.Combinatorics.Species.Labelled where

import qualified MathObj.PowerSeries as PowerSeries

import Data.Lub (parCommute, HasLub(..), flatLub)

import NumericPrelude
import PreludeBase hiding (cycle)


facts :: [Integer]
facts = 1 : zipWith (*) [1..] facts

-- This is a nice idea, but the EGF library is too slow!!
--
-- instance Species (EGF.T Integer) where
--   singleton = EGF.fromCoeffs [0,1]
--   set       = EGF.fromCoeffs $ repeat 1
--   list      = EGF.fromCoeffs facts
--   o         = EGF.compose
--   nonEmpty  (EGF.Cons (_:xs)) = EGF.Cons (0:xs)
--   nonEmpty  x = x
--
-- labelled :: EGF.T Integer -> [Integer]
-- labelled = EGF.coeffs
--
-- Sigh.  Just compute explicitly with normal power series and
-- zip/unzip with factorial denominators as necessary.

newtype LazyRational = LR { unLR :: Rational }
  deriving (Eq, Ord, Additive.C, ZeroTestable.C, Field.C)

instance HasLub LazyRational where
  lub = flatLub

instance Show LazyRational where
  show (LR r) = show r

instance Ring.C LazyRational where
  (*) = parCommute lazyTimes
    where lazyTimes (LR 0) _ = LR 0
          lazyTimes (LR 1) x = x
          lazyTimes (LR a) (LR b) = LR (a*b)
  fromInteger = LR . fromInteger

newtype Labelled = Labelled (PowerSeries.T LazyRational)
  deriving (Additive.C, Ring.C, Differential.C, Show)

instance Species Labelled where
  singleton = Labelled $ PowerSeries.fromCoeffs [0,1]
  set       = Labelled $ PowerSeries.fromCoeffs (map (LR . (1%)) facts)
  cycle     = Labelled $ PowerSeries.fromCoeffs (0 : map (LR . (1%)) [1..])
  o (Labelled f) (Labelled g) = Labelled $ PowerSeries.compose f g
  nonEmpty (Labelled (PowerSeries.Cons (_:xs))) = Labelled (PowerSeries.Cons (0:xs))
  nonEmpty x = x

  (Labelled (PowerSeries.Cons (x:_))) .: Labelled (PowerSeries.Cons ~(_:xs))
    = Labelled (PowerSeries.Cons (x:xs))


labelled :: Labelled -> [Integer]
labelled (Labelled f) = map numerator . zipWith (*) (map fromInteger facts) . map unLR $ PowerSeries.coeffs f
