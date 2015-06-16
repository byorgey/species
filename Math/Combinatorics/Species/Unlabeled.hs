{-# LANGUAGE CPP #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Math.Combinatorics.Species.CycleIndex
-- Copyright   :  (c) Brent Yorgey 2010
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@cis.upenn.edu
-- Stability   :  experimental
--
-- An interpretation of species as ordinary generating functions,
-- which count unlabeled structures.
--
-----------------------------------------------------------------------------

module Math.Combinatorics.Species.Unlabeled
    ( unlabeled, unlabelled ) where

import           Math.Combinatorics.Species.AST
import           Math.Combinatorics.Species.AST.Instances (reflect)
import           Math.Combinatorics.Species.Class
import           Math.Combinatorics.Species.CycleIndex
import           Math.Combinatorics.Species.NewtonRaphson
import           Math.Combinatorics.Species.Types

import qualified MathObj.PowerSeries                      as PS

import qualified Algebra.Differential                     as Differential

import           NumericPrelude
#if MIN_VERSION_numeric_prelude(0,2,0)
#else
import           PreludeBase                              hiding (cycle)
#endif

ciErr :: String -> a
ciErr op = error ("unlabeled " ++ op ++ " must go via cycle index series.")

instance Differential.C GF where
  differentiate = ciErr "differentiation"

instance Species GF where
  singleton         = gfFromCoeffs [0,1]
  set               = gfFromCoeffs (repeat 1)
  cycle             = gfFromCoeffs (0 : repeat 1)
  bracelet          = gfFromCoeffs (0 : repeat 1)
  o                 = ciErr "composition"
  (><)              = ciErr "cartesian product"
  (@@)              = ciErr "functor composition"
  ofSize s p        = (liftGF . PS.lift1 $ filterCoeffs p) s
  ofSizeExactly s n = (liftGF . PS.lift1 $ selectIndex n) s

  rec f             = case newtonRaphsonRec f 100 of
                        Nothing -> error $
                          "Unable to express " ++ show f ++ " in the form T = TX*R(T)."
                        Just ls -> ls

unlabeledCoeffs :: GF -> [Integer]
unlabeledCoeffs (GF p) = PS.coeffs p ++ repeat 0

-- | Extract the coefficients of an ordinary generating function as a
--   list of Integers.  In particular, @'unlabeled' s '!!'  n@ is the
--   number of unlabeled @s@-structures on an underlying set of size
--   @n@ (@unlabeled s@ is guaranteed to be infinite).  For example:
--
-- > > take 10 $ unlabeled octopi
-- > [0,1,2,3,5,7,13,19,35,59]
--
--   gives the number of unlabeled octopi on 0, 1, 2, 3, ... 9 elements.
--
--   Actually, the above is something of a white lie, as you may have
--   already realized by looking at the input type of 'unlabeled',
--   which is 'SpeciesAST' rather than the expected 'GF'.  The reason
--   is that although products and sums of unlabeled species
--   correspond to products and sums of ordinary generating functions,
--   other operations such as composition and differentiation do not!
--   In order to compute an ordinary generating function for a species
--   defined in terms of composition and/or differentiation, we must
--   compute the cycle index series for the species and then convert
--   it to an ordinary generating function.  So 'unlabeled' actually
--   works by first reifying the species to an AST and checking which
--   operations are used in its definition, and then choosing to work
--   with cycle index series or directly with (much faster) ordinary
--   generating functions as appropriate.
unlabeled :: SpeciesAST -> [Integer]
unlabeled s
  | needsCI s = unlabeledCoeffs . zToGF . reflect $ s
  | otherwise = unlabeledCoeffs . reflect $ s

-- | A synonym for 'unlabeled', since both spellings are acceptable.
unlabelled :: SpeciesAST -> [Integer]
unlabelled = unlabeled
