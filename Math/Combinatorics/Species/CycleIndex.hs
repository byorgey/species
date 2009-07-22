{-# LANGUAGE NoImplicitPrelude 
           , FlexibleInstances
  #-}

-- | An instance of 'Species' for cycle index series.  For details on
--   cycle index series, see \"Combinatorial Species and Tree-Like
--   Structures\", chapter 1.
module Math.Combinatorics.Species.CycleIndex 
    ( zToEGF
    , zToGF
    ) where

import Math.Combinatorics.Species.Types
import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Labelled

import qualified MathObj.PowerSeries as PowerSeries
import qualified MathObj.MultiVarPolynomial as MVP
import qualified MathObj.Monomial as Monomial
import qualified MathObj.FactoredRational as FQ

import qualified Algebra.Ring as Ring

import qualified Data.Map as M
import Data.List (genericReplicate, genericDrop, groupBy, sort, intercalate)
import Data.Function (on)
import Control.Arrow ((&&&), first, second)

import NumericPrelude
import PreludeBase hiding (cycle)

instance Species CycleIndex where
  singleton = CI $ MVP.x 1
  set       = ciFromMonomials . map partToMonomial . concatMap intPartitions $ [0..]

  cycle     = ciFromMonomials . concatMap cycleMonomials $ [1..]

  o = liftCI2 MVP.compose

  ofSize s p = (liftCI . MVP.lift1 $ filter (p . Monomial.pDegree)) s
  ofSizeExactly s n = (liftCI . MVP.lift1 $
                        ( takeWhile ((==n) . Monomial.pDegree)
                        . dropWhile ((<n) . Monomial.pDegree))) s
                         

  (CI (MVP.Cons (x:_))) .: (CI (MVP.Cons (y:ys))) = CI $ MVP.Cons (x:rest)
    where rest | Monomial.pDegree y == 0 = ys
               | otherwise               = (y:ys)

-- | Convert an integer partition to the corresponding monomial in the
--   cycle index series for the species of sets.
partToMonomial :: [(Integer, Integer)] -> Monomial.T Rational
partToMonomial js = Monomial.Cons (zCoeff js) (M.fromList js)

-- | @'zCoeff' js@ is the coefficient of the corresponding monomial in
--   the cycle index series for the species of sets.
zCoeff :: [(Integer, Integer)] -> Rational
zCoeff js = toRational $ 1 / aut js

-- | @aut js@ is is the number of automorphisms of a permutation with
--   cycle type @js@ (i.e. a permutation which has @n@ cycles of size
--   @i@ for each @(i,n)@ in @js@).
aut :: [(Integer, Integer)] -> FQ.T
aut = product . map (\(b,e) -> FQ.factorial e * (fromInteger b)^e)

-- | Generate all partitions of an integer.  In particular, if @p@ is
--   an element of the list output by @intPartitions n@, then @sum
--   . map (uncurry (*)) $ p == n@.
--
--   Also, the partitions are generated in an order corresponding to
--   the Ord instance for 'Monomial'.
intPartitions :: Integer -> [[(Integer, Integer)]]
intPartitions n = intPartitions' n n
  where intPartitions' :: Integer -> Integer -> [[(Integer,Integer)]]
        intPartitions' 0 _ = [[]]
        intPartitions' n 0 = []
        intPartitions' n k =
          [ if (j == 0) then js else (k,j):js
            | j <- reverse [0..n `div` k]
            , js <- intPartitions' (n - j*k) (min (k-1) (n - j*k)) ]

-- | @cycleMonomials d@ generates all monomials of partition degree
--   @d@ in the cycle index series for the species C of cycles.
cycleMonomials :: Integer -> [Monomial.T Rational]
cycleMonomials n = map cycleMonomial ds
  where n' = fromIntegral n
        ds = sort . FQ.divisors $ n'
        cycleMonomial d = Monomial.Cons (FQ.eulerPhi (n' / d) % n)
                                        (M.singleton (n `div` (toInteger d)) (toInteger d))

-- | Convert a cycle index series to an exponential generating
--   function:  F(x) = Z_F(x,0,0,0,...).
zToEGF :: CycleIndex -> EGF
zToEGF (CI (MVP.Cons xs))
  = EGF . PowerSeries.fromCoeffs . map LR
  . insertZeros
  . concatMap (\(c,as) -> case as of { [] -> [(0,c)] ; [(1,p)] -> [(p,c)] ; _ -> [] })
  . map (Monomial.coeff &&& (M.assocs . Monomial.powers))
  $ xs

-- | Convert a cycle index series to an ordinary generating function:
--   F~(x) = Z_F(x,x^2,x^3,...).
zToGF :: CycleIndex -> GF
zToGF (CI (MVP.Cons xs))
  = GF . PowerSeries.fromCoeffs . map numerator
  . insertZeros
  . map ((fst . head) &&& (sum . map snd))
  . groupBy ((==) `on` fst)
  . map ((sum . map (uncurry (*)) . M.assocs . Monomial.powers) &&& Monomial.coeff)
  $ xs

-- | Since cycle index series use a sparse representation, not every
--   power of x may be present after converting to an ordinary or
--   exponential generating function; 'insertZeros' inserts
--   coefficients of zero where necessary.
insertZeros :: Ring.C a => [(Integer, a)] -> [a]
insertZeros = insertZeros' [0..]
  where
    insertZeros' _ [] = []
    insertZeros' (n:ns) ((pow,c):pcs) 
      | n < pow   = genericReplicate (pow - n) 0 
                    ++ insertZeros' (genericDrop (pow - n) (n:ns)) ((pow,c):pcs)
      | otherwise = c : insertZeros' ns pcs
