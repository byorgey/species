{-# LANGUAGE NoImplicitPrelude
           , GeneralizedNewtypeDeriving
           , FlexibleContexts
           , DeriveDataTypeable
           , TypeFamilies
           , EmptyDataDecls
  #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Math.Combinatorics.Species.Structures
-- Copyright   :  (c) Brent Yorgey 2010
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@cis.upenn.edu
-- Stability   :  experimental
--
-- Types used for expressing generic structures when enumerating
-- species.
--
-----------------------------------------------------------------------------

module Math.Combinatorics.Species.Structures
    ( -- * Structure functors
      -- $struct

      Void
    , Unit(..)
    , Const(..)
    , Id(..)
    , Sum(..)
    , Prod(..)
    , Comp(..)
    , Cycle(..)
    , Set(..)
    , Star(..)

    , Mu(..), Interp

    ) where

import NumericPrelude
import PreludeBase
import Data.List (intercalate)

import Data.Typeable

--------------------------------------------------------------------------------
--  Structure functors  --------------------------------------------------------
--------------------------------------------------------------------------------

-- $struct
-- Functors used in building up structures for species
-- generation. Many of these functors are already defined elsewhere,
-- in other packages; but to avoid a plethora of imports, inconsistent
-- naming/instance schemes, etc., we just redefine them here.

-- | The (constantly) void functor.
data Void a
  deriving Typeable
instance Functor Void where
  fmap _ _ = undefined
instance Show (Void a) where
  show _   = undefined

-- | The (constantly) unit functor.
data Unit a = Unit
  deriving (Typeable, Show)
instance Functor Unit where
  fmap _ Unit = Unit

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
newtype Id a = Id a
  deriving Typeable
instance Functor Id where
  fmap f (Id x) = Id (f x)
instance (Show a) => Show (Id a) where
  show (Id x) = show x

-- | Functor coproduct.
data Sum f g a = Inl (f a) | Inr (g a)
instance (Functor f, Functor g) => Functor (Sum f g) where
  fmap f (Inl fa) = Inl (fmap f fa)
  fmap f (Inr ga) = Inr (fmap f ga)
instance (Show (f a), Show (g a)) => Show (Sum f g a) where
  show (Inl fa) = "inl(" ++ show fa ++ ")"
  show (Inr ga) = "inr(" ++ show ga ++ ")"
instance (Typeable1 f, Typeable1 g) => Typeable1 (Sum f g) where
  typeOf1 x = mkTyConApp (mkTyCon "Math.Combinatorics.Species.Types.Sum") [typeOf1 (getF x), typeOf1 (getG x)]
    where getF :: Sum f g a -> f a
          getF = undefined
          getG :: Sum f g a -> g a
          getG = undefined

-- | Functor product.
data Prod f g a = Prod (f a) (g a)
instance (Functor f, Functor g) => Functor (Prod f g) where
  fmap f (Prod fa ga) = Prod (fmap f fa) (fmap f ga)
instance (Show (f a), Show (g a)) => Show (Prod f g a) where
  show (Prod x y) = show (x,y)
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

-- | Cycle structure.  A value of type @'Cycle' a@ is implemented as
--   @[a]@, but thought of as a directed cycle.
newtype Cycle a = Cycle { getCycle :: [a] }
  deriving (Functor, Typeable)
instance (Show a) => Show (Cycle a) where
  show (Cycle xs) = "<" ++ intercalate "," (map show xs) ++ ">"

-- | Set structure.  A value of type @'Set' a@ is implemented as @[a]@,
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

-- XXX add some examples for Mu/Interp

-- | Higher-order fixpoint. @'Mu' f a@ is morally isomorphic to @f
--   ('Mu' f) a@, except that we actually need a level of indirection.
--   In fact @'Mu' f a@ is isomorphic to @'Interp' f ('Mu' f) a@; @f@
--   is a code which is interpreted by the 'Interp' type function.
data Mu f a = Mu { unMu :: Interp f (Mu f) a }
  deriving Typeable

-- | Interpretation type function for codes for higher-order type
--   constructors, used as arguments to the higher-order fixpoint 'Mu'.
type family Interp f self :: * -> *

