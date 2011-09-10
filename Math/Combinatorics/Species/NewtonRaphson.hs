{-# LANGUAGE NoImplicitPrelude
           , CPP
  #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Math.Combinatorics.Species.CycleIndex
-- Copyright   :  (c) Brent Yorgey 2010
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@cis.upenn.edu
-- Stability   :  experimental
--
-- The Newton-Raphson iterative method for computing with recursive
-- species.  Any species @T@ which can be written in the form @T =
-- X*R(T)@ (the species of "@R@-enriched rooted trees") may be
-- computed by a quadratically converging iterative process.  In fact
-- we may also compute species of the form @T = N + X*R(T)@ for any
-- integer species @N@, by iteratively computing @T' = X*R(T' + N)@
-- and then adding @N@.
--
-----------------------------------------------------------------------------

module Math.Combinatorics.Species.NewtonRaphson
    (
      newtonRaphsonIter
    , newtonRaphson
    , newtonRaphsonRec
    , solveForR
    ) where

import NumericPrelude
#if MIN_VERSION_numeric_prelude(0,2,0)
#else
import PreludeBase
#endif

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.AST
import Math.Combinatorics.Species.AST.Instances (reflect)
import Math.Combinatorics.Species.Simplify

import Data.Typeable

import Control.Monad (guard)
import Data.List (delete)

-- | A single iteration of the Newton-Raphson method.
--   @newtonRaphsonIter r k a@ assumes that @a@ is a species having
--   contact of order @k@ with species @t = x '*' (r ``o`` t)@ (that
--   is, @a@ and @t@ agree on all label sets of size up to and
--   including @k@), and returns a new species with contact of order
--   @2k+2@ with @t@.
--
--   See BLL section 3.3.
newtonRaphsonIter :: Species s => s -> Integer -> s -> s
newtonRaphsonIter r k a = a + sum as
  where p = x * (r `o` a)
        q = x * (oneHole r `o` a)
        ps = map (p `ofSizeExactly`) [k+1..2*k+2]
        qs = map (q `ofSizeExactly`) [1..k+1]
        as = zipWith (+) ps
               (map (sum . zipWith (*) qs) $ map reverse (inits' as))

-- | Lazier version of inits.
inits' :: [a] -> [[a]]
inits' xs = [] : inits'' xs
  where inits'' []     = []
        inits'' (x:xs) = map (x:) (inits' xs)

-- | Given a species @r@ and a desired accuracy @k@, @'newtonRaphson'
--   r k@ computes a species which has contact at least @k@ with the
--   species @t = x '*' (r ``o`` t)@.
newtonRaphson :: Species s => s -> Integer -> s
newtonRaphson r n = newtonRaphson' zero 0
  where newtonRaphson' a k
          | k >= n = a
          | otherwise = newtonRaphson' (newtonRaphsonIter r k a) (2*k + 2)

-- | @'newtonRaphsonRec' f k@ tries to compute the recursive species
--   represented by the code @f@ up to order at least @k@, using
--   Newton-Raphson iteration.  Returns 'Nothing' if @f@ cannot be
--   written in the form @f = X*R(f)@ for some species @R@.
newtonRaphsonRec :: (ASTFunctor f, Species s) => f -> Integer -> Maybe s
newtonRaphsonRec code k = fmap (\(n,r) -> n + newtonRaphson r k) (solveForR code)

-- | Given a code @f@ representing a recursive species, try to find an
--   integer species N and species R such that @f = N + X*R(f)@.  If
--   such species can be found, return @'Just' (N,R)@; otherwise
--   return 'Nothing'.
solveForR :: (ASTFunctor f, Species s) => f -> Maybe (s, s)
solveForR code = do
  let terms = sumOfProducts . erase' $ apply code (TRec code)
  guard . not . null $ terms

  -- If there is a constant term, it will be the first one; pull it
  -- out.
  let (n, terms') = case terms of
                      ([One] : ts) -> (One, ts)
                      ([N n] : ts) -> (N n, ts)
                      ts          -> (Zero, ts)

  -- Now we need to be able to factor an X out of the rest.
  guard $ all (X `elem`) terms'

  -- XXX this is wrong, what if there are still occurrences of X remaining?
  -- Now replace every recursive occurrence by (n + X).
  let r = foldr1 (+) $ map ( foldr1 (*)
                           . map (substRec code (n + x))
                           . delete X)
                       terms'

  return (reflect n, reflect r)

