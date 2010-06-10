{-# LANGUAGE NoImplicitPrelude
  #-}

-- | Newton-Raphson's iterative method for computing with recursive
--   species.
module Math.Combinatorics.Species.NewtonRaphson
    (
      newtonRaphsonIter
    , inits'
    , newtonRaphson
    , newtonRaphsonRec
    , solveForR
    ) where

import NumericPrelude
import PreludeBase

import Math.Combinatorics.Species
import Math.Combinatorics.Species.AST
import Math.Combinatorics.Species.AST.Instances (reflectU)
import Math.Combinatorics.Species.Simplify

import Data.Typeable

import Control.Monad (guard)
import Data.List (delete)

-- | @newtonRaphson r k a@ assumes that @a@ is a species having
--   contact of order @k@ with species @t = x * (r `o` t)@ (that is, @a@
--   and @t@ agree on all label sets of size up to and including @k@),
--   and returns a new species with contact of order @2k+2@ with @t@.
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

inits' xs = [] : inits'' xs
inits'' []     = []
inits'' (x:xs) = map (x:) (inits' xs)

-- | Given a species @r@ and a desired accuracy @k@, @newtonRaphson r
--   k@ computes a species which has contact at least @k@ with the
--   species @t = x * (r `o` t)@.
newtonRaphson :: Species s => s -> Integer -> s
newtonRaphson r n = newtonRaphson' 0 0
  where newtonRaphson' a k
          | k >= n = a
          | otherwise = newtonRaphson' (newtonRaphsonIter r k a) (2*k + 2)

newtonRaphsonRec :: (ASTFunctor f, Species s) => f -> Integer -> Maybe s
newtonRaphsonRec code k = fmap (\(n,r) -> n + newtonRaphson r k) (solveForR code)

solveForR :: (ASTFunctor f, Species s) => f -> Maybe (s, s)
solveForR code = do
  let terms = sumOfProducts . erase' $ apply code (Rec code)
  guard . not . null $ terms

  -- If there is a constant term, it will be the first one; pull it
  -- out.
  let (n, terms') = case terms of
                      ([UOne] : ts) -> (UOne, ts)
                      ([UN n] : ts) -> (UN n, ts)
                      ts          -> (UZero, ts)

  -- Now we need to be able to factor an X out of the rest.
  guard $ all (UX `elem`) terms'

  -- Now replace every recursive occurrence by (n + X).
  let r = foldr1 (+) $ map ( foldr1 (*)
                           . map (substRec code (n + x))
                           . delete UX)
                       terms'

  return (reflectU n, reflectU r)

