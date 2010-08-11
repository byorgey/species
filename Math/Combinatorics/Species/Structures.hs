{-# LANGUAGE NoImplicitPrelude
           , GeneralizedNewtypeDeriving
           , FlexibleContexts
           , DeriveDataTypeable
           , TypeFamilies
           , EmptyDataDecls
           , TypeOperators
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
    , (:+:)(..)
    , (:*:)(..)
    , (:.:)(..)
    , Cycle(..)
    , Set(..)
    , Star(..)

    , Mu(..), Interp

    ) where

import NumericPrelude
import PreludeBase
import Data.List (intercalate, foldl', delete, inits, tails)

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
  fmap = undefined
instance Show (Void a) where
  show = undefined

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
data (f :+: g) a = Inl (f a) | Inr (g a)
instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (Inl fa) = Inl (fmap f fa)
  fmap f (Inr ga) = Inr (fmap f ga)
instance (Show (f a), Show (g a)) => Show ((f :+: g) a) where
  show (Inl fa) = "inl(" ++ show fa ++ ")"
  show (Inr ga) = "inr(" ++ show ga ++ ")"
instance (Typeable1 f, Typeable1 g) => Typeable1 (f :+: g) where
  typeOf1 x = mkTyConApp (mkTyCon "Math.Combinatorics.Species.Types.(:+:)") [typeOf1 (getF x), typeOf1 (getG x)]
    where getF :: (f :+: g) a -> f a
          getF = undefined
          getG :: (f :+: g) a -> g a
          getG = undefined

-- | Functor product.
data (f :*: g) a = f a :*: g a

pFst :: (f :*: g) a -> f a
pFst (x :*: y) = x

pSnd :: (f :*: g) a -> g a
pSnd (x :*: y) = y

pSwap :: (f :*: g) a -> (g :*: f) a
pSwap (x :*: y) = y :*: x

instance (Functor f, Functor g) => Functor (f :*: g) where
  fmap f (fa :*: ga) = fmap f fa :*: fmap f ga
instance (Show (f a), Show (g a)) => Show ((f :*: g) a) where
  show (x :*: y) = show (x,y)
instance (Typeable1 f, Typeable1 g) => Typeable1 (f :*: g) where
  typeOf1 x = mkTyConApp (mkTyCon "Math.Combinatorics.Species.Types.(:*:)") [typeOf1 (getF x), typeOf1 (getG x)]
    where getF :: (f :*: g) a -> f a
          getF = undefined
          getG :: (f :*: g) a -> g a
          getG = undefined

-- | Functor composition.
data (f :.: g) a = Comp { unComp :: (f (g a)) }
instance (Functor f, Functor g) => Functor (f :.: g) where
  fmap f (Comp fga) = Comp (fmap (fmap f) fga)
instance (Show (f (g a))) => Show ((f :.: g) a) where
  show (Comp x) = show x
instance (Typeable1 f, Typeable1 g) => Typeable1 (f :.: g) where
  typeOf1 x = mkTyConApp (mkTyCon "Math.Combinatorics.Species.Types.(:.:)") [typeOf1 (getF x), typeOf1 (getG x)]
    where getF :: (f :.: g) a -> f a
          getF = undefined
          getG :: (f :.: g) a -> g a
          getG = undefined

-- | Cycle structure.  A value of type @'Cycle' a@ is implemented as
--   @[a]@, but thought of as a directed cycle.
newtype Cycle a = Cycle { getCycle :: [a] }
  deriving (Functor, Typeable)
instance (Show a) => Show (Cycle a) where
  show (Cycle xs) = "<" ++ intercalate "," (map show xs) ++ ">"
instance Eq a => Eq (Cycle a) where
  Cycle xs == Cycle ys = any (==ys) (rotations xs)
    where rotations xs = zipWith (++)  (tails xs)
                                       (inits xs)

-- | Set structure.  A value of type @'Set' a@ is implemented as @[a]@,
--   but thought of as an unordered set.
newtype Set a = Set { getSet :: [a] }
  deriving (Functor, Typeable)
instance (Show a) => Show (Set a) where
  show (Set xs) = "{" ++ intercalate "," (map show xs) ++ "}"
instance Eq a => Eq (Set a) where
  Set xs == Set ys = xs `subBag` ys && ys `subBag` xs
    where subBag b = null . foldl' (flip delete) b

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

-- Note, the above instance does not properly display structures
-- arising from higher derivatives, since the different holes are not
-- distinguished (although they should be).  This could be fixed by
-- prefixing all the Original elements with some special character;
-- then you could tell the difference between, say, "*" and "~*" (if ~
-- was the special character).  However, this solution seems a bit
-- heavyweight.  Multiple differentiation is not that common, and you
-- can always do case analysis to correctly figure out the structure;
-- it's just the String representations which would be misleading.

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

