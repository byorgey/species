{-# LANGUAGE NoImplicitPrelude
           , EmptyDataDecls
           , TypeFamilies
           , TypeOperators
           , FlexibleContexts
           , GeneralizedNewtypeDeriving
           , DeriveDataTypeable
  #-}

-- | Some common types used by the species library.
module Math.Combinatorics.Species.Types
    ( -- * Lazy multiplication
      
      LazyRing(..)
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

      -- * Higher-order Show

    , ShowF(..)
    , RawString(..)

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

      -- * Type-level species
      -- $typespecies    
      
    , Z, S, X, (:+:), (:*:), (:.:), Der, E, C, (:><:), (:@:)
    , StructureF
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
--  Higher-order Show  ---------------------------------------------------------
--------------------------------------------------------------------------------

-- | When generating species, we build up a functor representing
--   structures of that species; in order to display generated
--   structures, we need to know that applying the computed functor to
--   a Showable type will also yield something Showable.
class Functor f => ShowF f where
  showF :: (Show a) => f a -> String

instance ShowF [] where
  showF = show

-- | 'RawString' is like String, but with a Show instance that doesn't
--   add quotes or do any escaping.  This is a (somewhat silly) hack
--   needed to implement a 'ShowF' instance for 'Comp'.
newtype RawString = RawString String
instance Show RawString where
  show (RawString s) = s

--------------------------------------------------------------------------------
--  Structure functors  --------------------------------------------------------
--------------------------------------------------------------------------------

-- $struct
-- Functors used in building up structures for species generation.

-- | The constant functor.
newtype Const x a = Const x
instance Functor (Const x) where
  fmap _ (Const x) = Const x
instance (Show x) => Show (Const x a) where
  show (Const x) = show x
instance (Show x) => ShowF (Const x) where
  showF = show
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
instance ShowF Identity where
  showF = show

-- | Functor coproduct.
newtype Sum f g a = Sum  { unSum  :: Either (f a) (g a) }
instance (Functor f, Functor g) => Functor (Sum f g) where
  fmap f (Sum (Left fa))  = Sum (Left (fmap f fa))
  fmap f (Sum (Right ga)) = Sum (Right (fmap f ga))
instance (Show (f a), Show (g a)) => Show (Sum f g a) where
  show (Sum x) = show x
instance (ShowF f, ShowF g) => ShowF (Sum f g) where
  showF (Sum (Left fa)) = "inl(" ++ showF fa ++ ")"
  showF (Sum (Right ga)) = "inr(" ++ showF ga ++ ")"
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
instance (ShowF f, ShowF g) => ShowF (Prod f g) where
  showF (Prod (fa, ga)) = "(" ++ showF fa ++ "," ++ showF ga ++ ")"
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
instance (ShowF f, ShowF g) => ShowF (Comp f g) where
  showF (Comp fga) = showF (fmap (RawString . showF) fga)
instance (Typeable1 f, Typeable1 g) => Typeable1 (Comp f g) where
  typeOf1 x = mkTyConApp (mkTyCon "Math.Combinatorics.Species.Types.Comp") [typeOf1 (getF x), typeOf1 (getG x)]
    where getF :: Comp f g a -> f a
          getF = undefined
          getG :: Comp f g a -> g a
          getG = undefined

-- | Cycle structure.  A value of type 'Cycle a' is implemented as
--   '[a]', but thought of as a directed cycle.
newtype Cycle a = Cycle [a]
  deriving (Functor, Typeable)
instance (Show a) => Show (Cycle a) where
  show (Cycle xs) = "<" ++ intercalate "," (map show xs) ++ ">"
instance ShowF Cycle where
  showF = show


-- | Set structure.  A value of type 'Set a' is implemented as '[a]',
--   but thought of as an unordered set.
newtype Set a = Set [a]
  deriving (Functor, Typeable)
instance (Show a) => Show (Set a) where
  show (Set xs) = "{" ++ intercalate "," (map show xs) ++ "}"
instance ShowF Set where
  showF = show

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
instance ShowF Star where
  showF = show

--------------------------------------------------------------------------------
--  Type-level species  --------------------------------------------------------
--------------------------------------------------------------------------------

-- $typespecies
-- Some constructor-less data types used as indices to 'SpeciesAlgT'
-- to reflect the species structure at the type level.  This is the
-- point at which we wish we were doing this in a dependently typed
-- language.

data Z
data S n
data X
data E
data C
data (:+:) f g
data (:*:) f g
data (:.:) f g
data (:><:) f g
data (:@:) f g
data Der f

-- | 'StructureF' is a type function which maps type-level species
--   descriptions to structure functors.  That is, a structure of the
--   species with type-level representation @s@, on the underlying set
--   @a@, has type @StructureF s a@.
type family StructureF t :: * -> *
type instance StructureF Z            = Const Integer
type instance StructureF (S s)        = Const Integer
type instance StructureF X            = Identity
type instance StructureF E            = Set
type instance StructureF C            = Cycle
type instance StructureF (f :+: g)    = Sum (StructureF f) (StructureF g)
type instance StructureF (f :*: g)    = Prod (StructureF f) (StructureF g)
type instance StructureF (f :.: g)    = Comp (StructureF f) (StructureF g)
type instance StructureF (f :><: g)   = Prod (StructureF f) (StructureF g)
type instance StructureF (f :@: g)    = Comp (StructureF f) (StructureF g)
type instance StructureF (Der f)      = Comp (StructureF f) Star

