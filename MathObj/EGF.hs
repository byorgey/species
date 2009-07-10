module MathObj.EGF where

import qualified Algebra.Additive as Additive
import qualified Algebra.Ring as Ring
import qualified Algebra.IntegralDomain as ID
import qualified Algebra.Field as Field
import qualified Algebra.ToInteger as ToInteger

import qualified Algebra.Differential as Differential
import qualified Algebra.ZeroTestable as ZeroTestable

import qualified MathObj.Polynomial as Poly

import Data.Maybe (isNothing, fromMaybe)
import Data.List (inits, tails, mapAccumL)
import Control.Applicative
import Data.Monoid hiding (Sum(..))

import PreludeBase    hiding (const)
import NumericPrelude hiding (negate)



-- NOTE this should really go in the Additive module!
newtype Sum a = Sum { getSum :: a }

instance Additive.C a => Monoid (Sum a) where
  mempty  = Sum zero
  mappend (Sum a) (Sum b) = Sum (a + b)



newtype T a = Cons {coeffs :: [a]} deriving (Ord)

{-# INLINE fromCoeffs #-}
fromCoeffs :: [a] -> T a
fromCoeffs = lift0

{-# INLINE lift0 #-}
lift0 :: [a] -> T a
lift0 = Cons

{-# INLINE lift1 #-}
lift1 :: ([a] -> [a]) -> (T a -> T a)
lift1 f (Cons x0) = Cons (f x0)

{-# INLINE lift2 #-}
lift2 :: ([a] -> [a] -> [a]) -> (T a -> T a -> T a)
lift2 f (Cons x0) (Cons x1) = Cons (f x0 x1)

{-# INLINE const #-}
const :: a -> T a
const x = lift0 [x]

instance Functor T where
  fmap f (Cons xs) = Cons (map f xs)

{-# INLINE appPrec #-}
appPrec :: Int
appPrec  = 10

instance (Show a) => Show (T a) where
  showsPrec p (Cons xs) =
    showParen (p >= appPrec) (showString "EGF.fromCoeffs " . shows xs)

{-# INLINE truncate #-}
truncate :: Int -> T a -> T a
truncate n = lift1 (take n)

{- |
Evaluate (truncated) egf's.
-}

{-# INLINE evaluate #-}
evaluate :: Field.C a => T a -> a -> a
evaluate (Cons y) = flip Poly.horner (zipWith (/) y facs)
  where facs = 1 : zipWith (*) Poly.progression facs

instance (Eq a, ZeroTestable.C a) => Eq (T a) where
    (Cons x) == (Cons y) = Poly.equal x y

{- * Series arithmetic for EGFs -}

add, sub :: (Additive.C a) => [a] -> [a] -> [a]
add = Poly.add
sub = Poly.sub

negate :: (Additive.C a) => [a] -> [a]
negate = Poly.negate

scale :: Ring.C a => a -> [a] -> [a]
scale = Poly.scale

-- This works but it's super inefficient!  e.g. try
--   mul (replicate 100 1) (replicate 100 1) :: [Integer]
--
-- mul :: Ring.C a => [a] -> [a] -> [a]
-- mul [] _ = []
-- mul _ [] = []
-- mul f@(x:xs) g@(y:ys) = integrate (x*y) (mul f' g + mul f g')
--   where f' = differentiate f
--         g' = differentiate g

-- binomial convolution.
-- is there a better/lazier way to do this?
mul :: ID.C a => [a] -> [a] -> [a]
mul [] _ = []
mul _ [] = []
mul f g = zipWith binomConv (inits $ Poly.progression) (convolve f g)
  where binomConv ns pairs = maybe 0 getSum
                           . mconcat
                           . map (fmap Sum)
                           $ zipWith (fmap . (*))
                               (binoms ns)
                               (map (fmap (uncurry (*))) pairs)

convolve :: [a] -> [b] -> [[Maybe (a,b)]]
convolve xs ys = takeWhile (not . all isNothing)
               $ zipWith (zipWith pair) (inits' xs) (map reverse $ inits' ys)
  where inits' = drop 1 . inits . (++ repeat Nothing) . map Just
        pair x y = (,) <$> x <*> y

-- Given an argument of the form [1..n], efficiently generate a list
-- of the binomial coefficients [(n choose 0) .. (n choose n)].
-- XXX better way to write this? as a zip with a tied knot?
binoms :: (ID.C a) => [a] -> [a]
binoms ns = one : (snd $ mapAccumL nextB one (zip (reverse ns) ns))
  where nextB b (m,d) = let x = b*m `div` d in (x,x)

instance (Additive.C a) => Additive.C (T a) where
    negate = lift1 Poly.negate
    (+)    = lift2 Poly.add
    (-)    = lift2 Poly.sub
    zero   = lift0 []

instance (ID.C a) => Ring.C (T a) where
    one           = const one
    fromInteger n = const (fromInteger n)
    (*)           = lift2 mul

differentiate :: [a] -> [a]
differentiate = safeTail
  where safeTail [] = []
        safeTail (x:xs) = xs

integrate :: a -> [a] -> [a]
integrate = (:)

instance ID.C a => Differential.C (T a) where
  differentiate = lift1 differentiate

compose :: (Ring.C a, ZeroTestable.C a) => T a -> T a -> T a
compose (Cons []) (Cons [])    = Cons []
compose (Cons (x:_)) (Cons []) = Cons [x]
compose (Cons xs) (Cons (y:ys)) =
  if isZero y
    then Cons (comp xs ys)
    else error "EGF.compose: inner series must not have an absolute term."

-- Exponential gf composition.  See Faa di Bruno's formula.
comp :: Ring.C a => [a] -> [a] -> [a]
comp = undefined -- XXX