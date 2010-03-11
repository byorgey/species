{-# LANGUAGE NoImplicitPrelude
           , GeneralizedNewtypeDeriving
           , PatternGuards
  #-}
-- | An interpretation of species as exponential generating functions,
--   which count labelled structures.
module Math.Combinatorics.Species.Labelled
    ( labelled
    ) where

-- A previous version of this module used an EGF library which
-- explicitly computed with EGF's.  However, it turned out to be much
-- slower than just computing explicitly with normal power series and
-- zipping/unzipping with factorial denominators as necessary, which
-- is the current approach.

import Math.Combinatorics.Species.Types
import Math.Combinatorics.Species.Class

import Math.Combinatorics.Species.AST
import Math.Combinatorics.Species.AST.Instances

import qualified MathObj.PowerSeries as PS
import qualified MathObj.FactoredRational as FQ

import NumericPrelude
import PreludeBase hiding (cycle)

facts :: [Integer]
facts = 1 : zipWith (*) [1..] facts

instance Species EGF where
  singleton         = egfFromCoeffs [0,1]
  set               = egfFromCoeffs (map (LR . (1%)) facts)
  cycle             = egfFromCoeffs (0 : map (LR . (1%)) [1..])
  o                 = liftEGF2 PS.compose
  cartesian         = liftEGF2 . PS.lift2 $ \xs ys -> zipWith3 mult xs ys (map fromIntegral facts)
    where mult x y z = x * y * z
  fcomp             = liftEGF2 . PS.lift2 $ \fs gs -> map (\(n,gn) -> let gn' = numerator . unLR $ gn
                                                                       in (fs `safeIndex` gn')
                                                                            * LR (toRational (FQ.factorial gn' / FQ.factorial n)))
                                                          (zip [0..] $ zipWith (*) (map fromIntegral facts) gs)
    where safeIndex [] _     = 0
          safeIndex (x:_)  0 = x
          safeIndex (_:xs) n = safeIndex xs (n-1)

  ofSize s p        = (liftEGF . PS.lift1 $ filterCoeffs p) s
  ofSizeExactly s n = (liftEGF . PS.lift1 $ selectIndex n) s

  rec f = reflect (Wrap (apply f (Rec f)))

-- | Extract the coefficients of an exponential generating function as
--   a list of Integers.  Since 'EGF' is an instance of 'Species', the
--   idea is that 'labelled' can be applied directly to an expression
--   of the Species DSL.  In particular, @labelled s !!  n@ is the
--   number of labelled s-structures on an underlying set of size n
--   (note that @labelled s@ is guaranteed to be an infinite list).
--   For example:
--
-- > > take 10 $ labelled octopi
-- > [0,1,3,14,90,744,7560,91440,1285200,20603520]
--
--   gives the number of labelled octopi on 0, 1, 2, 3, ... 9 elements.

labelled :: EGF -> [Integer]
labelled (EGF f) = (++repeat 0)
                 . map numerator
                 . zipWith (*) (map fromInteger facts)
                 . map unLR
                 $ PS.coeffs f

