{-# LANGUAGE NoImplicitPrelude
           , EmptyDataDecls
           , TypeFamilies
           , TypeOperators
           , FlexibleContexts
           , GeneralizedNewtypeDeriving
           , DeriveDataTypeable
           , UndecidableInstances
  #-}

-- | Some common types used by the species library, along with some
--   utility functions.
module Math.Combinatorics.Species.Types
    ( -- * Miscellaneous

      CycleType

      -- * Lazy multiplication

    , LazyRing(..)
    , LazyQ
    , LazyZ

      -- * Series types

    , EGF(..)
    , egfFromCoeffs
    , liftEGF
    , liftEGF2

    , GF(..)
    , gfFromCoeffs
    , liftGF
    , liftGF2

    , CycleIndex(..)
    , ciFromMonomials
    , liftCI
    , liftCI2

    , filterCoeffs
    , selectIndex

      -- * Structure functors
      -- $struct

    , Const(..)
    , Identity(..)
    , Sum(..)
    , Prod(..)
    , Comp(..)
    , Cycle(..)
    , Set(..)
    , Star(..)

    , Mu(..), Res

    ) where

import Data.List (intercalate, genericReplicate)
import NumericPrelude
import PreludeBase

import qualified MathObj.PowerSeries as PS
import qualified MathObj.MultiVarPolynomial as MVP
import qualified MathObj.Monomial as Monomial

import qualified Algebra.Additive as Additive
import qualified Algebra.Ring as Ring
import qualified Algebra.Differential as Differential
import qualified Algebra.ZeroTestable as ZeroTestable
import qualified Algebra.Field as Field

import Data.Lub (parCommute, HasLub(..), flatLub)

import Data.Typeable

-- | A representation of the cycle type of a permutation.  If @c ::
--   CycleType@ and @(k,n) `elem` c@, then the permutation has @n@
--   cycles of size @k@.
type CycleType = [(Integer, Integer)]

--------------------------------------------------------------------------------
--  Lazy multiplication  -------------------------------------------------------
--------------------------------------------------------------------------------

-- | If @T@ is an instance of @Ring@, then @LazyRing T@ is isomorphic
--   to T but with a lazy multiplication: @0 * undefined = undefined * 0
--   = 0@.
newtype LazyRing a = LR { unLR :: a }
  deriving (Eq, Ord, Additive.C, ZeroTestable.C, Field.C)

instance HasLub (LazyRing a) where
  lub = flatLub

instance Show a => Show (LazyRing a) where
  show (LR r) = show r

instance (Eq a, Ring.C a) => Ring.C (LazyRing a) where
  (*) = parCommute lazyTimes
    where lazyTimes (LR 0) _ = LR 0
          lazyTimes (LR 1) x = x
          lazyTimes (LR a) (LR b) = LR (a*b)
  fromInteger = LR . fromInteger

type LazyQ = LazyRing Rational
type LazyZ = LazyRing Integer

--------------------------------------------------------------------------------
--  Series types  --------------------------------------------------------------
--------------------------------------------------------------------------------

-- | Exponential generating functions, for counting labelled species.
newtype EGF = EGF (PS.T LazyQ)
  deriving (Additive.C, Ring.C, Differential.C, Show)

egfFromCoeffs :: [LazyQ] -> EGF
egfFromCoeffs = EGF . PS.fromCoeffs

liftEGF :: (PS.T LazyQ -> PS.T LazyQ) -> EGF -> EGF
liftEGF f (EGF x) = EGF (f x)

liftEGF2 :: (PS.T LazyQ -> PS.T LazyQ -> PS.T LazyQ)
         -> EGF -> EGF -> EGF
liftEGF2 f (EGF x) (EGF y) = EGF (f x y)

-- | Ordinary generating functions, for counting unlabelled species.
newtype GF = GF (PS.T Integer)
  deriving (Additive.C, Ring.C, Show)

gfFromCoeffs :: [Integer] -> GF
gfFromCoeffs = GF . PS.fromCoeffs

liftGF :: (PS.T Integer -> PS.T Integer) -> GF -> GF
liftGF f (GF x) = GF (f x)

liftGF2 :: (PS.T Integer -> PS.T Integer -> PS.T Integer)
         -> GF -> GF -> GF
liftGF2 f (GF x) (GF y) = GF (f x y)

-- | Cycle index series.
newtype CycleIndex = CI (MVP.T Rational)
  deriving (Additive.C, Ring.C, Differential.C, Show)

ciFromMonomials :: [Monomial.T Rational] -> CycleIndex
ciFromMonomials = CI . MVP.Cons

liftCI :: (MVP.T Rational -> MVP.T Rational)
        -> CycleIndex -> CycleIndex
liftCI f (CI x) = CI (f x)

liftCI2 :: (MVP.T Rational -> MVP.T Rational -> MVP.T Rational)
        -> CycleIndex -> CycleIndex -> CycleIndex
liftCI2 f (CI x) (CI y) = CI (f x y)

-- Some series utility functions

-- | Filter the coefficients of a series according to a predicate.
filterCoeffs :: (Additive.C a) => (Integer -> Bool) -> [a] -> [a]
filterCoeffs p = zipWith (filterCoeff p) [0..]
    where filterCoeff p n x | p n       = x
                            | otherwise = Additive.zero

-- | Set every coefficient of a series to 0 except the selected
--   index. Truncate any trailing zeroes.
selectIndex :: (Ring.C a, Eq a) => Integer -> [a] -> [a]
selectIndex n xs = xs'
    where mx = safeIndex n xs
          safeIndex _ []     = Nothing
          safeIndex 0 (x:_)  = Just x
          safeIndex n (_:xs) = safeIndex (n-1) xs
          xs' = case mx of
                  Just 0 -> []
                  Just x -> genericReplicate n 0 ++ [x]
                  _      -> []

--------------------------------------------------------------------------------
--  Structure functors  --------------------------------------------------------
--------------------------------------------------------------------------------

-- $struct
-- Functors used in building up structures for species
-- generation. Many of these functors are already defined elsewhere,
-- in other packages; but to avoid a plethora of imports, inconsistent
-- naming/instance schemes, etc., we just redefine them here.

-- | The constant functor.
newtype Const x a = Const x
instance Functor (Const x) where
  fmap _ (Const x) = Const x
instance (Show x) => Show (Const x a) where
  show (Const x) = show x
instance Typeable2 Const where
  typeOf2 _ = mkTyConApp (mkTyCon "Const") []
instance Typeable x => Typeable1 (Const x) where
  typeOf1 = typeOf1Default

-- | The identity functor.
newtype Identity a = Identity a
  deriving Typeable
instance Functor Identity where
  fmap f (Identity x) = Identity (f x)
instance (Show a) => Show (Identity a) where
  show (Identity x) = show x

-- | Functor coproduct.
newtype Sum f g a = Sum  { unSum  :: Either (f a) (g a) }
instance (Functor f, Functor g) => Functor (Sum f g) where
  fmap f (Sum (Left fa))  = Sum (Left (fmap f fa))
  fmap f (Sum (Right ga)) = Sum (Right (fmap f ga))
instance (Show (f a), Show (g a)) => Show (Sum f g a) where
  show (Sum (Left fa)) = "inl(" ++ show fa ++ ")"
  show (Sum (Right ga)) = "inr(" ++ show ga ++ ")"
instance (Typeable1 f, Typeable1 g) => Typeable1 (Sum f g) where
  typeOf1 x = mkTyConApp (mkTyCon "Math.Combinatorics.Species.Types.Sum") [typeOf1 (getF x), typeOf1 (getG x)]
    where getF :: Sum f g a -> f a
          getF = undefined
          getG :: Sum f g a -> g a
          getG = undefined

-- | Functor product.
newtype Prod f g a = Prod { unProd :: (f a, g a) }
instance (Functor f, Functor g) => Functor (Prod f g) where
  fmap f (Prod (fa, ga)) = Prod (fmap f fa, fmap f ga)
instance (Show (f a), Show (g a)) => Show (Prod f g a) where
  show (Prod x) = show x
instance (Typeable1 f, Typeable1 g) => Typeable1 (Prod f g) where
  typeOf1 x = mkTyConApp (mkTyCon "Math.Combinatorics.Species.Types.Prod") [typeOf1 (getF x), typeOf1 (getG x)]
    where getF :: Prod f g a -> f a
          getF = undefined
          getG :: Prod f g a -> g a
          getG = undefined

-- | Functor composition.
data Comp f g a = Comp { unComp :: (f (g a)) }
instance (Functor f, Functor g) => Functor (Comp f g) where
  fmap f (Comp fga) = Comp (fmap (fmap f) fga)
instance (Show (f (g a))) => Show (Comp f g a) where
  show (Comp x) = show x
instance (Typeable1 f, Typeable1 g) => Typeable1 (Comp f g) where
  typeOf1 x = mkTyConApp (mkTyCon "Math.Combinatorics.Species.Types.Comp") [typeOf1 (getF x), typeOf1 (getG x)]
    where getF :: Comp f g a -> f a
          getF = undefined
          getG :: Comp f g a -> g a
          getG = undefined

-- | Cycle structure.  A value of type 'Cycle a' is implemented as
--   '[a]', but thought of as a directed cycle.
newtype Cycle a = Cycle { getCycle :: [a] }
  deriving (Functor, Typeable)
instance (Show a) => Show (Cycle a) where
  show (Cycle xs) = "<" ++ intercalate "," (map show xs) ++ ">"

-- | Set structure.  A value of type 'Set a' is implemented as '[a]',
--   but thought of as an unordered set.
newtype Set a = Set { getSet :: [a] }
  deriving (Functor, Typeable)
instance (Show a) => Show (Set a) where
  show (Set xs) = "{" ++ intercalate "," (map show xs) ++ "}"

-- | 'Star' is isomorphic to 'Maybe', but with a more useful 'Show'
--   instance for our purposes.  Used to implement species
--   differentiation.
data Star a = Star | Original a
  deriving (Typeable)
instance Functor Star where
  fmap _ Star = Star
  fmap f (Original a) = Original (f a)
instance (Show a) => Show (Star a) where
  show Star = "*"
  show (Original a) = show a

-- Recursive species.

data Mu f a = Mu { unMu :: Res f (Mu f) a }
  deriving Typeable

type family Res f self :: * -> *

