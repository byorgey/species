{-# LANGUAGE NoImplicitPrelude
           , CPP
           , GADTs
           , TypeFamilies
           , KindSignatures
           , FlexibleContexts
           , RankNTypes
           , TypeOperators
  #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Math.Combinatorics.Species.AST
-- Copyright   :  (c) Brent Yorgey 2010
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@cis.upenn.edu
-- Stability   :  experimental
--
-- Various data structures representing reified combinatorial species
-- expressions.  See also "Math.Combinatorics.Species.AST.Instances".
--
-----------------------------------------------------------------------------

module Math.Combinatorics.Species.AST
    (
      -- * Basic species expression AST
      SpeciesAST(..)

      -- * Typed, sized species expression AST
    , TSpeciesAST(..)

      -- ** Size annotations
    , SizedSpeciesAST(..)
    , interval, annI, getI, stripI

      -- ** Existentially wrapped AST
    , ESpeciesAST(..), wrap, unwrap
    , erase, erase', annotate

      -- * ASTFunctor class (codes for higher-order functors)
    , ASTFunctor(..)

      -- * Miscellaneous AST operations

    , needsCI

    , substRec

    ) where

import Math.Combinatorics.Species.Structures
import Math.Combinatorics.Species.Util.Interval
import qualified Math.Combinatorics.Species.Util.Interval as I

import Data.Typeable
import Unsafe.Coerce

import Data.Maybe (fromMaybe)

import NumericPrelude
#if MIN_VERSION_numeric_prelude(0,2,0)
#else
import PreludeBase hiding (cycle)
#endif

------------------------------------------------------------
--  Untyped AST  -------------------------------------------
------------------------------------------------------------

-- | A basic, untyped AST type for species expressions, for easily
-- doing things like analysis, simplification, deriving isomorphisms,
-- and so on.  Converting between 'SpeciesAST' and the typed variant
-- 'ESpeciesAST' can be done with 'annotate' and 'erase'.
data SpeciesAST where
  Zero          :: SpeciesAST
  One           :: SpeciesAST
  N             :: Integer -> SpeciesAST
  X             :: SpeciesAST
  E             :: SpeciesAST
  C             :: SpeciesAST
  L             :: SpeciesAST
  Subset        :: SpeciesAST
  KSubset       :: Integer -> SpeciesAST
  Elt           :: SpeciesAST
  (:+)         :: SpeciesAST -> SpeciesAST -> SpeciesAST
  (:*)         :: SpeciesAST -> SpeciesAST -> SpeciesAST
  (:.)         :: SpeciesAST -> SpeciesAST -> SpeciesAST
  (:><)        :: SpeciesAST -> SpeciesAST -> SpeciesAST
  (:@)         :: SpeciesAST -> SpeciesAST -> SpeciesAST
  Der           :: SpeciesAST -> SpeciesAST
  OfSize        :: SpeciesAST -> (Integer -> Bool) -> SpeciesAST
  OfSizeExactly :: SpeciesAST -> Integer -> SpeciesAST
  NonEmpty      :: SpeciesAST -> SpeciesAST
  Rec           :: ASTFunctor f => f -> SpeciesAST
  Omega         :: SpeciesAST

------------------------------------------------------------
--  Typed, sized AST  --------------------------------------
------------------------------------------------------------

-- | A variant of 'SpeciesAST' with a phantom type parameter which
--   also reflects the structure, so we can write
--   quasi-dependently-typed functions over species, in particular for
--   species enumeration.
--
--   Of course, the non-uniform type parameter means that
--   'TSpeciesAST' cannot be an instance of the 'Species' class; for
--   that purpose the existential wrapper 'ESpeciesAST' is provided.
--
--   'TSpeciesAST' is defined via mutual recursion with
--   'SizedSpeciesAST', which pairs a 'TSpeciesAST' with an interval
--   annotation indicating (a conservative approximation of) the label
--   set sizes for which the species actually yields any structures;
--   this information makes enumeration faster and also prevents it
--   from getting stuck in infinite recursion in some cases.  A value
--   of 'SizedSpeciesAST' is thus an annotated species expression tree
--   with interval annotations at every node.
data TSpeciesAST (s :: * -> *) where
   TZero     :: TSpeciesAST Void
   TOne      :: TSpeciesAST Unit
   TN        :: Integer -> TSpeciesAST (Const Integer)
   TX        :: TSpeciesAST Id
   TE        :: TSpeciesAST Set
   TC        :: TSpeciesAST Cycle
   TL        :: TSpeciesAST []
   TSubset   :: TSpeciesAST Set
   TKSubset  :: Integer -> TSpeciesAST Set
   TElt      :: TSpeciesAST Id
   (:+::)    :: SizedSpeciesAST f -> SizedSpeciesAST g -> TSpeciesAST (f :+: g)
   (:*::)    :: SizedSpeciesAST f -> SizedSpeciesAST g -> TSpeciesAST (f :*: g)
   (:.::)    :: SizedSpeciesAST f -> SizedSpeciesAST g -> TSpeciesAST (f :.: g)
   (:><::)   :: SizedSpeciesAST f -> SizedSpeciesAST g -> TSpeciesAST (f :*: g)
   (:@::)    :: SizedSpeciesAST f -> SizedSpeciesAST g -> TSpeciesAST (f :.: g)
   TDer      :: SizedSpeciesAST f -> TSpeciesAST (f :.: Star)
   TOfSize   :: SizedSpeciesAST f -> (Integer -> Bool) -> TSpeciesAST f
   TOfSizeExactly :: SizedSpeciesAST f -> Integer -> TSpeciesAST f
   TNonEmpty :: SizedSpeciesAST f -> TSpeciesAST f
   TRec      :: ASTFunctor f => f -> TSpeciesAST (Mu f)

   TOmega    :: TSpeciesAST Void

data SizedSpeciesAST (s :: * -> *) where
  Sized :: Interval -> TSpeciesAST s -> SizedSpeciesAST s

-- | Given a 'TSpeciesAST', compute (a conservative approximation of)
--   the interval of label set sizes on which the species yields any
--   structures.
interval :: TSpeciesAST s -> Interval
interval TZero                = emptyI
interval TOne                 = zero
interval (TN n)               = zero
interval TX                   = one
interval TE                   = natsI
interval TC                   = fromI one
interval TL                   = natsI
interval TSubset              = natsI
interval (TKSubset k)         = fromI (fromInteger k)
interval TElt                 = fromI one
interval (f :+:: g)           = getI f `I.union` getI g
interval (f :*:: g)           = getI f + getI g
interval (f :.:: g)           = getI f * getI g
interval (f :><:: g)          = getI f `I.intersect` getI g
interval (f :@:: g)           = natsI
    -- Note, the above interval for functor composition is obviously
    -- overly conservative.  To do this right we'd have to compute the
    -- generating function for g --- and actually it would depend on
    -- whether we were doing labeled or unlabeled enumeration, which
    -- we don't know at this point.
interval (TDer f)             = decrI (getI f)
interval (TOfSize f p)        = fromI $ smallestIn (getI f) p
interval (TOfSizeExactly f n) = fromInteger n `I.intersect` getI f
interval (TNonEmpty f)        = fromI one `I.intersect` getI f
interval (TRec f)             = interval (apply f TOmega)
interval TOmega               = omegaI

-- | Find the smallest integer in the given interval satisfying a predicate.
smallestIn :: Interval -> (Integer -> Bool) -> NatO
smallestIn i p = case filter p (toList i) of
                   []    -> I.omega
                   (x:_) -> fromIntegral x


-- | Annotate a 'TSpeciesAST' with the interval of label set sizes for
--   which it yields structures.
annI :: TSpeciesAST s -> SizedSpeciesAST s
annI s = Sized (interval s) s

-- | Strip the interval annotation from a 'SizedSpeciesAST'.
stripI :: SizedSpeciesAST s -> TSpeciesAST s
stripI (Sized _ s) = s

-- | Retrieve the interval annotation from a 'SizedSpeciesAST'.
getI :: SizedSpeciesAST s -> Interval
getI (Sized i _) = i

-- | An existential wrapper to hide the phantom type parameter to
--   'SizedSpeciesAST', so we can make it an instance of 'Species'.
data ESpeciesAST where
  Wrap :: Typeable s => SizedSpeciesAST s -> ESpeciesAST

-- | Construct an 'ESpeciesAST' from a 'TSpeciesAST' by adding an
--   appropriate interval annotation and hiding the type.
wrap :: Typeable s => TSpeciesAST s -> ESpeciesAST
wrap = Wrap . annI

-- | Unwrap an existential wrapper to get out a typed AST.  You can
--   get out any type you like as long as it is the right one.
--
--   CAUTION: Don't try this at home!
unwrap :: Typeable s => ESpeciesAST -> TSpeciesAST s
unwrap (Wrap f) = gcast1'
                . stripI
                $ f
  where gcast1' x = r
          where r = if typeOf1 (getArg x) == typeOf1 (getArg r)
                      then unsafeCoerce x
                      else error ("unwrap: cast failed. Wanted " ++
                                  show (typeOf1 (getArg r)) ++
                                  ", instead got " ++
                                  show (typeOf1 (getArg x)))
                getArg :: c x -> x ()
                getArg = undefined

-- | Erase the type and interval information from an existentially
-- wrapped species AST.
erase :: ESpeciesAST -> SpeciesAST
erase (Wrap s) = erase' (stripI s)

-- | Erase the type and interval information from a typed species AST.
erase' :: TSpeciesAST f -> SpeciesAST
erase' TZero                = Zero
erase' TOne                 = One
erase' (TN n)               = N n
erase' TX                   = X
erase' TE                   = E
erase' TC                   = C
erase' TL                   = L
erase' TSubset              = Subset
erase' (TKSubset k)         = KSubset k
erase' TElt                 = Elt
erase' (f :+:: g)           = erase' (stripI f) :+ erase' (stripI g)
erase' (f :*:: g)           = erase' (stripI f) :* erase' (stripI g)
erase' (f :.:: g)           = erase' (stripI f) :. erase' (stripI g)
erase' (f :><:: g)          = erase' (stripI f) :>< erase' (stripI g)
erase' (f :@:: g)           = erase' (stripI f) :@ erase' (stripI g)
erase' (TDer f)             = Der . erase' . stripI $ f
erase' (TOfSize f p)        = OfSize (erase' . stripI $ f) p
erase' (TOfSizeExactly f k) = OfSizeExactly (erase' . stripI $ f) k
erase' (TNonEmpty f)        = NonEmpty . erase' . stripI $ f
erase' (TRec f)             = Rec f
erase' TOmega               = Omega

-- | Reconstruct the type and interval annotations on a species AST.
annotate :: SpeciesAST -> ESpeciesAST
annotate Zero                = wrap TZero
annotate One                 = wrap TOne
annotate (N n)               = wrap (TN n)
annotate X                   = wrap TX
annotate E                   = wrap TE
annotate C                   = wrap TC
annotate L                   = wrap TL
annotate Subset              = wrap TSubset
annotate (KSubset k)         = wrap (TKSubset k)
annotate Elt                 = wrap TElt
annotate (f :+ g)           = annotate f + annotate g
  where Wrap f + Wrap g      = wrap $ f :+:: g
annotate (f :* g)           = annotate f * annotate g
  where Wrap f * Wrap g      = wrap $ f :*:: g
annotate (f :. g)           = annotate f . annotate g
  where Wrap f . Wrap g      = wrap $ f :.:: g
annotate (f :>< g)          = annotate f >< annotate g
  where Wrap f >< Wrap g     = wrap $ f :><:: g
annotate (f :@ g)           = annotate f @@ annotate g
  where Wrap f @@ Wrap g     = wrap $ f :@:: g
annotate (Der f)             = der $ annotate f
  where der (Wrap f)         = wrap (TDer f)
annotate (OfSize f p)        = ofSize $ annotate f
  where ofSize (Wrap f)      = wrap $ TOfSize f p
annotate (OfSizeExactly f k) = ofSize $ annotate f
  where ofSize (Wrap f)      = wrap $ TOfSizeExactly f k
annotate (NonEmpty f)        = nonEmpty $ annotate f
  where nonEmpty (Wrap f)    = wrap $ TNonEmpty f
annotate (Rec f)             = wrap $ TRec f
annotate Omega               = wrap TOmega

------------------------------------------------------------
--  ASTFunctor class  --------------------------------------
------------------------------------------------------------

-- | 'ASTFunctor' is a type class for codes which can be interpreted
--   (via the 'Interp' type family) as higher-order functors over
--   species expressions.  The 'apply' method allows such codes to be
--   applied to a species AST.  The indirection is needed to implement
--   recursive species.
class (Typeable f, Show f, Typeable (Interp f (Mu f))) => ASTFunctor f where
  apply :: Typeable g => f -> TSpeciesAST g -> TSpeciesAST (Interp f g)

------------------------------------------------------------
--  Miscellaneous AST operations  --------------------------
------------------------------------------------------------

-- | 'needsCI' is a predicate which checks whether a species expression
--   uses any of the operations which are not supported directly by
--   ordinary generating functions (composition, differentiation,
--   cartesian product, and functor composition), and hence need cycle
--   index series.
needsCI :: SpeciesAST -> Bool
needsCI L            = True
needsCI (f :+ g)    = needsCI f || needsCI g
needsCI (f :* g)    = needsCI f || needsCI g
needsCI (_ :. _)    = True
needsCI (_ :>< _)   = True
needsCI (_ :@ _)    = True
needsCI (Der _)      = True
needsCI (OfSize f _) = needsCI f
needsCI (OfSizeExactly f _) = needsCI f
needsCI (NonEmpty f) = needsCI f
needsCI (Rec _)      = True    -- Newton-Raphson iteration uses composition
needsCI _            = False

-- | Substitute an expression for recursive occurrences.
substRec :: ASTFunctor f => f -> SpeciesAST -> SpeciesAST -> SpeciesAST
substRec c e (f :+ g)                          = substRec c e f :+ substRec c e g
substRec c e (f :* g)                          = substRec c e f :* substRec c e g
substRec c e (f :. g)                          = substRec c e f :. substRec c e g
substRec c e (f :>< g)                         = substRec c e f :>< substRec c e g
substRec c e (f :@ g)                          = substRec c e f :@ substRec c e g
substRec c e (Der f)                            = Der (substRec c e f)
substRec c e (OfSize f p)                       = OfSize (substRec c e f) p
substRec c e (OfSizeExactly f k)                = OfSizeExactly (substRec c e f) k
substRec c e (NonEmpty f)                       = NonEmpty (substRec c e f)
substRec c e (Rec c')
  | (show . typeOf $ c) == (show . typeOf $ c')  = e
substRec _ _ f                                   = f
