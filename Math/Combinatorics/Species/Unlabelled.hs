module Math.Combinatorics.Species.Unlabelled where

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Algebra
import Math.Combinatorics.Species.CycleIndex

import qualified MathObj.PowerSeries as PowerSeries

import qualified Algebra.Differential as Differential

import NumericPrelude
import PreludeBase hiding (cycle)

newtype Unlabelled = Unlabelled (PowerSeries.T Integer)
  deriving (Additive.C, Ring.C, Show)

instance Differential.C Unlabelled where
  differentiate = error "unlabelled differentiation must go via cycle index series."

instance Species Unlabelled where
  singleton = Unlabelled $ PowerSeries.fromCoeffs [0,1]
  set       = Unlabelled $ PowerSeries.fromCoeffs (repeat 1)
  cycle     = set
  o         = error "unlabelled composition must go via cycle index series."
  nonEmpty (Unlabelled (PowerSeries.Cons (_:xs))) = Unlabelled (PowerSeries.Cons (0:xs))
  nonEmpty x = x

  (Unlabelled (PowerSeries.Cons (x:_))) .: Unlabelled (PowerSeries.Cons xs)
    = Unlabelled (PowerSeries.Cons (x:tail xs))

unlabelledCoeffs :: Unlabelled -> [Integer]
unlabelledCoeffs (Unlabelled p) = PowerSeries.coeffs p

unlabelled :: SpeciesAlg -> [Integer]
unlabelled s 
  | hasDer s || hasComp s = unlabelledCoeffs . zToUnlabelled . reflect $ s
  | otherwise             = unlabelledCoeffs . reflect $ s
