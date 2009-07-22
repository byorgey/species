{-# LANGUAGE NoImplicitPrelude
           , EmptyDataDecls
           , TypeFamilies
           , TypeOperators
           , FlexibleContexts
           , GeneralizedNewtypeDeriving
  #-}

-- | Some common types used by the species library.
module Math.Combinatorics.Species.Types
    ( -- * Lazy multiplication
      
      LazyRing(..)
    , LazyQ
    , LazyZ

      -- * Series types

    , EGF(..)
    , GF(..)
    , CycleIndex(..)

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
    , Star(..)

      -- * Type-level species
      -- $typespecies    
      
    , Z, S, X, (:+:), (:*:), (:.:), Der, E, C, NonEmpty
    , StructureF
    ) where

import Data.List (intercalate)
import NumericPrelude
import PreludeBase

import qualified MathObj.PowerSeries as PowerSeries
import qualified MathObj.MultiVarPolynomial as MVP

import qualified Algebra.Additive as Additive
import qualified Algebra.Ring as Ring
import qualified Algebra.Differential as Differential
import qualified Algebra.ZeroTestable as ZeroTestable
import qualified Algebra.Field as Field

import Data.Lub (parCommute, HasLub(..), flatLub)

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
newtype EGF = EGF (PowerSeries.T LazyQ)
  deriving (Additive.C, Ring.C, Differential.C, Show)

-- | Ordinary generating functions, for counting unlabelled species.
newtype GF = GF (PowerSeries.T Integer)
  deriving (Additive.C, Ring.C, Show)

-- | Cycle index series.
newtype CycleIndex = CI (MVP.T Rational)
  deriving (Additive.C, Ring.C, Differential.C, Show)

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

-- | The identity functor.
newtype Identity a = Identity a
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
  showF (Sum (Left fa)) = "Left " ++ showF fa
  showF (Sum (Right ga)) = "Right " ++ showF ga

-- | Functor product.
newtype Prod f g a = Prod { unProd :: (f a, g a) }
instance (Functor f, Functor g) => Functor (Prod f g) where
  fmap f (Prod (fa, ga)) = Prod (fmap f fa, fmap f ga)
instance (Show (f a), Show (g a)) => Show (Prod f g a) where
  show (Prod x) = show x
instance (ShowF f, ShowF g) => ShowF (Prod f g) where
  showF (Prod (fa, ga)) = "(" ++ showF fa ++ "," ++ showF ga ++ ")"

-- | Functor composition.
data Comp f g a = Comp { unComp :: (f (g a)) }
instance (Functor f, Functor g) => Functor (Comp f g) where
  fmap f (Comp fga) = Comp (fmap (fmap f) fga)
instance (Show (f (g a))) => Show (Comp f g a) where
  show (Comp x) = show x
instance (ShowF f, ShowF g) => ShowF (Comp f g) where
  showF (Comp fga) = showF (fmap (RawString . showF) fga)

-- | Cycle structure.  A value of type 'Cycle a' is implemented as
--   '[a]', but thought of as a directed cycle.
newtype Cycle a = Cycle [a]
instance Functor Cycle where
  fmap f (Cycle xs) = Cycle (fmap f xs)
instance (Show a) => Show (Cycle a) where
  show (Cycle xs) = "{" ++ intercalate "," (map show xs) ++ "}"
instance ShowF Cycle where
  showF = show

-- | 'Star' is isomorphic to 'Maybe', but with a more useful 'Show'
--   instance for our purposes.  Used to implement species
--   differentiation.
data Star a = Star | Original a
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
data (:+:) f g
data (:*:) f g
data (:.:) f g
data Der f
data E
data C
data NonEmpty f

-- | 'StructureF' is a type function which maps type-level species
--   descriptions to structure functors.  That is, a structure of the
--   species with type-level representation @s@, on the underlying set
--   @a@, has type @StructureF s a@.
type family StructureF t :: * -> *
type instance StructureF Z            = Const Integer
type instance StructureF (S s)        = Const Integer
type instance StructureF X            = Identity
type instance StructureF (f :+: g)    = Sum (StructureF f) (StructureF g)
type instance StructureF (f :*: g)    = Prod (StructureF f) (StructureF g)
type instance StructureF (f :.: g)    = Comp (StructureF f) (StructureF g)
type instance StructureF (Der f)      = Comp (StructureF f) Star
type instance StructureF E            = []
type instance StructureF C            = Cycle
type instance StructureF (NonEmpty f) = StructureF f

