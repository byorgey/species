-- | An interpretation of species as ordinary generating functions,
--   which count unlabelled structures.
module Math.Combinatorics.Species.Unlabelled 
    ( unlabelled ) where

import Math.Combinatorics.Species.Types
import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Algebra
import Math.Combinatorics.Species.CycleIndex

import qualified MathObj.PowerSeries as PowerSeries

import qualified Algebra.Differential as Differential

import NumericPrelude
import PreludeBase hiding (cycle)

instance Differential.C GF where
  differentiate = error "unlabelled differentiation must go via cycle index series."

instance Species GF where
  singleton = GF $ PowerSeries.fromCoeffs [0,1]
  set       = GF $ PowerSeries.fromCoeffs (repeat 1)
  cycle     = set
  o         = error "unlabelled composition must go via cycle index series."
  nonEmpty (GF (PowerSeries.Cons (_:xs))) = GF (PowerSeries.Cons (0:xs))
  nonEmpty x = x

  (GF (PowerSeries.Cons (x:_))) .: GF (PowerSeries.Cons xs)
    = GF (PowerSeries.Cons (x:tail xs))

unlabelledCoeffs :: GF -> [Integer]
unlabelledCoeffs (GF p) = PowerSeries.coeffs p

-- | Extract the coefficients of an ordinary generating function as a
--   list of Integers.  In particular, @unlabelled s !!  n@ is the
--   number of unlabelled s-structures on an underlying set of size n.
--   For example:
--
-- > > take 10 $ unlabelled octopi
-- > [0,1,2,3,5,7,13,19,35,59]
--
--   gives the number of unlabelled octopi on 0, 1, 2, 3, ... 9 elements.
--
--   Actually, the above is something of a white lie, as you may have
--   already realized by looking at the input type of 'unlabelled',
--   which is 'SpeciesAlg' rather than the expected 'GF'.  The
--   reason is that although products and sums of unlabelled species
--   correspond to products and sums of ordinary generating functions,
--   composition and differentiation do not!  In order to compute an
--   ordinary generating function for a species defined in terms of
--   composition and/or differentiation, we must compute the cycle
--   index series for the species and then convert it to an ordinary
--   generating function.  So 'unlabelled' actually works by first
--   reifying the species to an AST and checking whether it uses
--   composition or differentiation, and using operations on cycle
--   index series if it does, and (much faster) operations directly on
--   ordinary generating functions otherwise.
unlabelled :: SpeciesAlg -> [Integer]
unlabelled s 
  | hasDer s || hasComp s = unlabelledCoeffs . zToGF . reflect $ s
  | otherwise             = unlabelledCoeffs . reflect $ s
