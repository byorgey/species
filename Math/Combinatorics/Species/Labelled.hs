{-# LANGUAGE NoImplicitPrelude 
           , GeneralizedNewtypeDeriving
  #-}
-- | An interpretation of species as exponential generating functions,
--   which count labelled structures.
module Math.Combinatorics.Species.Labelled 
    ( labelled
    ) where

import Math.Combinatorics.Species.Types
import Math.Combinatorics.Species.Class

import qualified MathObj.PowerSeries as PowerSeries

import NumericPrelude
import PreludeBase hiding (cycle)

facts :: [Integer]
facts = 1 : zipWith (*) [1..] facts

instance Species EGF where
  singleton = EGF $ PowerSeries.fromCoeffs [0,1]
  set       = EGF $ PowerSeries.fromCoeffs (map (LR . (1%)) facts)
  cycle     = EGF $ PowerSeries.fromCoeffs (0 : map (LR . (1%)) [1..])
  o (EGF f) (EGF g) = EGF $ PowerSeries.compose f g
  nonEmpty (EGF (PowerSeries.Cons (_:xs))) = EGF (PowerSeries.Cons (0:xs))
  nonEmpty x = x

  (EGF (PowerSeries.Cons (x:_))) .: EGF (PowerSeries.Cons ~(_:xs))
    = EGF (PowerSeries.Cons (x:xs))

-- | Extract the coefficients of an exponential generating function as
--   a list of Integers.  Since 'EGF' is an instance of
--   'Species', the idea is that 'labelled' can be applied directly to
--   an expression of the Species DSL.  In particular, @labelled s !!
--   n@ is the number of labelled s-structures on an underlying set of
--   size n.  For example:
--
-- > > take 10 $ labelled octopi
-- > [0,1,3,14,90,744,7560,91440,1285200,20603520]
--
--   gives the number of labelled octopi on 0, 1, 2, 3, ... 9 elements.

labelled :: EGF -> [Integer]
labelled (EGF f) = map numerator . zipWith (*) (map fromInteger facts) . map unLR $ PowerSeries.coeffs f

-- A previous version of this module used an EGF library which
-- explicitly computed with EGF's.  However, it turned out to be much
-- slower than just computing explicitly with normal power series and
-- zipping/unzipping with factorial denominators as necessary, which
-- is the current approach.
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
