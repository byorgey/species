-- | An interpretation of species as ordinary generating functions,
--   which count unlabelled structures.
module Math.Combinatorics.Species.Unlabelled 
    ( unlabelled ) where

import Math.Combinatorics.Species.Types
import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Algebra
import Math.Combinatorics.Species.CycleIndex

import qualified MathObj.PowerSeries as PS

import qualified Algebra.Differential as Differential

import NumericPrelude
import PreludeBase hiding (cycle)

needsCI :: String -> a
needsCI op = error (op ++ " must go via cycle index series.")

instance Differential.C GF where
  differentiate = needsCI "unlabelled differentiation"

instance Species GF where
  singleton         = gfFromCoeffs [0,1]
  set               = gfFromCoeffs (repeat 1)
  cycle             = set
  o                 = needsCI "unlabelled composition"
  ofSize s p        = (liftGF . PS.lift1 $ filterCoeffs p) s
  ofSizeExactly s n = (liftGF . PS.lift1 $ selectIndex n) s
  cartesian         = needsCI "unlabelled cartesian product"

unlabelledCoeffs :: GF -> [Integer]
unlabelledCoeffs (GF p) = PS.coeffs p

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
  | needsZ s  = unlabelledCoeffs . zToGF . reflect $ s
  | otherwise = unlabelledCoeffs . reflect $ s
