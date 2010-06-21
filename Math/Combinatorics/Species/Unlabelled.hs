-- | An interpretation of species as ordinary generating functions,
--   which count unlabelled structures.
module Math.Combinatorics.Species.Unlabelled
    ( unlabelled ) where

import Math.Combinatorics.Species.Types
import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.AST
import Math.Combinatorics.Species.AST.Instances (reflect)
import Math.Combinatorics.Species.CycleIndex
import Math.Combinatorics.Species.NewtonRaphson

import qualified MathObj.PowerSeries as PS

import qualified Algebra.Differential as Differential

import NumericPrelude
import PreludeBase hiding (cycle)

needsCI :: String -> a
needsCI op = error ("unlabelled " ++ op ++ " must go via cycle index series.")

instance Differential.C GF where
  differentiate = needsCI "differentiation"

instance Species GF where
  singleton         = gfFromCoeffs [0,1]
  set               = gfFromCoeffs (repeat 1)
  cycle             = set
  o                 = needsCI "composition"
  cartesian         = needsCI "cartesian product"
  fcomp             = needsCI "functor composition"
  ofSize s p        = (liftGF . PS.lift1 $ filterCoeffs p) s
  ofSizeExactly s n = (liftGF . PS.lift1 $ selectIndex n) s

  rec f = case newtonRaphsonRec f 100 of
            Nothing -> error $ "Unable to express " ++ show f ++ " in the form T = TX*R(T)."
            Just ls -> ls

unlabelledCoeffs :: GF -> [Integer]
unlabelledCoeffs (GF p) = PS.coeffs p ++ repeat 0

-- | Extract the coefficients of an ordinary generating function as a
--   list of Integers.  In particular, @unlabelled s !!  n@ is the
--   number of unlabelled s-structures on an underlying set of size n
--   (@unlabelled s@ is guaranteed to be infinite).  For example:
--
-- > > take 10 $ unlabelled octopi
-- > [0,1,2,3,5,7,13,19,35,59]
--
--   gives the number of unlabelled octopi on 0, 1, 2, 3, ... 9 elements.
--
--   Actually, the above is something of a white lie, as you may have
--   already realized by looking at the input type of 'unlabelled',
--   which is 'ESpeciesAST' rather than the expected 'GF'.  The reason
--   is that although products and sums of unlabelled species
--   correspond to products and sums of ordinary generating functions,
--   other operations such as composition and differentiation do not!
--   In order to compute an ordinary generating function for a species
--   defined in terms of composition and/or differentiation, we must
--   compute the cycle index series for the species and then convert
--   it to an ordinary generating function.  So 'unlabelled' actually
--   works by first reifying the species to an AST and checking which
--   operations are used in its definition, and then choosing to work
--   with cycle index series or directly with (much faster) ordinary
--   generating functions as appropriate.
unlabelled :: ESpeciesAST -> [Integer]
unlabelled s
  | needsZE s  = unlabelledCoeffs . zToGF . reflect $ s
  | otherwise = unlabelledCoeffs . reflect $ s
