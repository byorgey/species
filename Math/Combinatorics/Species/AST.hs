{-# LANGUAGE NoImplicitPrelude
           , GADTs
           , TypeFamilies
           , KindSignatures
           , FlexibleContexts
  #-}

-- | A data structure to reify combinatorial species.
module Math.Combinatorics.Species.AST
    (
      SpeciesAST(..), SizedSpeciesAST(..)
    , interval, annI, getI, stripI
    , ESpeciesAST(..)
    , ASTFunctor(..)

    , needsZ, needsZE

    ) where

import Math.Combinatorics.Species.Structures
import Math.Combinatorics.Species.Util.Interval
import qualified Math.Combinatorics.Species.Util.Interval as I

import Data.Typeable

import NumericPrelude
import PreludeBase hiding (cycle)

-- | Reified combinatorial species.  Note that 'SpeciesAST' has a
--   phantom type parameter which also reflects the structure, so we
--   can write quasi-dependently-typed functions over species, in
--   particular for species enumeration.
--
--   Of course, the non-uniform type parameter means that
--   'SpeciesAST' cannot be an instance of the 'Species' class;
--   for that purpose the existential wrapper 'ESpeciesAST' is
--   provided.
--
--   'SpeciesAST' is defined via mutual recursion with
--   'SizedSpeciesAST', which pairs a 'SpeciesAST' with an interval
--   annotation indicating (a conservative approximation of) the label
--   set sizes for which the species actually yields any structures.
--   A value of 'SizedSpeciesAST' is thus an annotated species
--   expression tree with interval annotations at every node.
data SpeciesAST (s :: * -> *) where
   Zero     :: SpeciesAST Void
   One      :: SpeciesAST Unit
   N        :: Integer -> SpeciesAST (Const Integer)
   X        :: SpeciesAST Id
   E        :: SpeciesAST Set
   C        :: SpeciesAST Cycle
   L        :: SpeciesAST []
   Subset   :: SpeciesAST Set
   KSubset  :: Integer -> SpeciesAST Set
   Elt      :: SpeciesAST Id
   (:+:)    :: SizedSpeciesAST f -> SizedSpeciesAST g -> SpeciesAST (Sum f g)
   (:*:)    :: SizedSpeciesAST f -> SizedSpeciesAST g -> SpeciesAST (Prod f g)
   (:.:)    :: SizedSpeciesAST f -> SizedSpeciesAST g -> SpeciesAST (Comp f g)
   (:><:)   :: SizedSpeciesAST f -> SizedSpeciesAST g -> SpeciesAST (Prod f g)
   (:@:)    :: SizedSpeciesAST f -> SizedSpeciesAST g -> SpeciesAST (Comp f g)
   Der      :: SizedSpeciesAST f -> SpeciesAST (Comp f Star)
   OfSize   :: SizedSpeciesAST f -> (Integer -> Bool) -> SpeciesAST f
   OfSizeExactly :: SizedSpeciesAST f -> Integer -> SpeciesAST f
   NonEmpty :: SizedSpeciesAST f -> SpeciesAST f
   Rec      :: ASTFunctor f => f -> SpeciesAST (Mu f)

   Omega    :: SpeciesAST Void

data SizedSpeciesAST (s :: * -> *) where
  Sized :: Interval -> SpeciesAST s -> SizedSpeciesAST s

-- | Given a 'SpeciesAST', compute (a conservative approximation of)
--   the interval of label set sizes on which the species yields any
--   structures.
interval :: SpeciesAST s -> Interval
interval Zero                = emptyI
interval One                 = 0
interval (N n)               = 0
interval X                   = 1
interval E                   = natsI
interval C                   = fromI 1
interval L                   = natsI
interval Subset              = natsI
interval (KSubset k)         = fromI (fromInteger k)
interval Elt                 = fromI 1
interval (f :+: g)           = getI f `I.union` getI g
interval (f :*: g)           = getI f + getI g
interval (f :.: g)           = getI f * getI g
interval (f :><: g)          = getI f `I.intersect` getI g
interval (f :@: g)           = natsI
    -- Note, the above interval for functor composition is obviously
    -- overly conservative.  To do this right we'd have to compute the
    -- generating function for g --- and actually it would depend on
    -- whether we were doing labelled or unlabelled enumeration, which
    -- we don't know at this point.
interval (Der f)             = decrI (getI f)
interval (OfSize f p)        = fromI $ smallestIn (getI f) p
interval (OfSizeExactly f n) = fromInteger n `I.intersect` getI f
interval (NonEmpty f)        = fromI 1 `I.intersect` getI f
interval (Rec f)             = interval (apply f Omega)
interval Omega               = omegaI

-- | Find the smallest integer in the given interval satisfying a predicate.
smallestIn :: Interval -> (Integer -> Bool) -> NatO
smallestIn i p = case filter p (toList i) of
                   []    -> I.omega
                   (x:_) -> fromIntegral x


-- | Annotate a 'SpeciesAST' with the interval of label set sizes for
--   which it yields structures.
annI :: SpeciesAST s -> SizedSpeciesAST s
annI s = Sized (interval s) s

-- | Strip the interval annotation from a 'SizedSpeciesAST'.
stripI :: SizedSpeciesAST s -> SpeciesAST s
stripI (Sized _ s) = s

-- | Retrieve the interval annotation.
getI :: SizedSpeciesAST s -> Interval
getI (Sized i _) = i

-- | Type class for codes which can be interpreted as higher-order
--   functors.
class (Typeable f, Show f, Typeable1 (Interp f (Mu f))) => ASTFunctor f where
  apply :: f -> SpeciesAST g -> SpeciesAST (Interp f g)

-- | 'needsZ' is a predicate which checks whether a species uses any
--   of the operations which are not supported directly by ordinary
--   generating functions (composition, differentiation, cartesian
--   product, and functor composition), and hence need cycle index
--   series.
needsZ :: SpeciesAST s -> Bool
needsZ L            = True
needsZ (f :+: g)    = needsZ (stripI f) || needsZ (stripI g)
needsZ (f :*: g)    = needsZ (stripI f) || needsZ (stripI g)
needsZ (_ :.: _)    = True
needsZ (_ :><: _)   = True
needsZ (_ :@: _)    = True
needsZ (Der _)      = True
needsZ (OfSize f _) = needsZ (stripI f)
needsZ (OfSizeExactly f _) = needsZ (stripI f)
needsZ (NonEmpty f) = needsZ (stripI f)
needsZ _            = False

-- | An existential wrapper to hide the phantom type parameter to
--   'SizedSpeciesAST', so we can make it an instance of 'Species'.
data ESpeciesAST where
  Wrap :: Typeable1 s => SizedSpeciesAST s -> ESpeciesAST

-- | A version of 'needsZ' for 'ESpeciesAST'.
needsZE :: ESpeciesAST -> Bool
needsZE (Wrap s) = needsZ (stripI s)