{-# LANGUAGE NoImplicitPrelude
           , GADTs
           , TypeFamilies
           , KindSignatures
           , FlexibleContexts
           , RankNTypes
  #-}

-- | A data structure to reify combinatorial species.
module Math.Combinatorics.Species.AST
    (
      SpeciesAST(..), SizedSpeciesAST(..)
    , interval, annI, getI, stripI
    , ESpeciesAST(..), wrap
    , ASTFunctor(..)

    , needsZ, needsZE

    , USpeciesAST(..), erase, erase', unerase
    , substRec

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
  apply :: Typeable1 g => f -> SpeciesAST g -> SpeciesAST (Interp f g)

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

-- | Smart wrap constructor which also adds an appropriate interval
--   annotation.
wrap :: Typeable1 s => SpeciesAST s -> ESpeciesAST
wrap = Wrap . annI

-- | A version of 'needsZ' for 'ESpeciesAST'.
needsZE :: ESpeciesAST -> Bool
needsZE (Wrap s) = needsZ (stripI s)

-- | A plain old untyped variant of the species AST, for more easily
--   doing things like analysis, simplification, deriving
--   isomorphisms, and so on.  Converting between 'ESpeciesAST' and
--   'USpeciesAST' can be done with 'erase' and 'unerase'.
data USpeciesAST where
  UZero          :: USpeciesAST
  UOne           :: USpeciesAST
  UN             :: Integer -> USpeciesAST
  UX             :: USpeciesAST
  UE             :: USpeciesAST
  UC             :: USpeciesAST
  UL             :: USpeciesAST
  USubset        :: USpeciesAST
  UKSubset       :: Integer -> USpeciesAST
  UElt           :: USpeciesAST
  (:+:%)         :: USpeciesAST -> USpeciesAST -> USpeciesAST
  (:*:%)         :: USpeciesAST -> USpeciesAST -> USpeciesAST
  (:.:%)         :: USpeciesAST -> USpeciesAST -> USpeciesAST
  (:><:%)        :: USpeciesAST -> USpeciesAST -> USpeciesAST
  (:@:%)         :: USpeciesAST -> USpeciesAST -> USpeciesAST
  UDer           :: USpeciesAST -> USpeciesAST
  UOfSize        :: USpeciesAST -> (Integer -> Bool) -> USpeciesAST
  UOfSizeExactly :: USpeciesAST -> Integer -> USpeciesAST
  UNonEmpty      :: USpeciesAST -> USpeciesAST
  URec           :: ASTFunctor f => f -> USpeciesAST
  UOmega         :: USpeciesAST

-- | Erase the type and interval information from a species AST.
erase :: ESpeciesAST -> USpeciesAST
erase (Wrap s) = erase' (stripI s)

erase' :: SpeciesAST f -> USpeciesAST
erase' Zero                = UZero
erase' One                 = UOne
erase' (N n)               = UN n
erase' X                   = UX
erase' E                   = UE
erase' C                   = UC
erase' L                   = UL
erase' Subset              = USubset
erase' (KSubset k)         = UKSubset k
erase' Elt                 = UElt
erase' (f :+: g)           = erase' (stripI f) :+:% erase' (stripI g)
erase' (f :*: g)           = erase' (stripI f) :*:% erase' (stripI g)
erase' (f :.: g)           = erase' (stripI f) :.:% erase' (stripI g)
erase' (f :><: g)          = erase' (stripI f) :><:% erase' (stripI g)
erase' (f :@: g)           = erase' (stripI f) :@:% erase' (stripI g)
erase' (Der f)             = UDer . erase' . stripI $ f
erase' (OfSize f p)        = UOfSize (erase' . stripI $ f) p
erase' (OfSizeExactly f k) = UOfSizeExactly (erase' . stripI $ f) k
erase' (NonEmpty f)        = UNonEmpty . erase' . stripI $ f
erase' (Rec f)             = URec f
erase' Omega               = UOmega

-- | Reconstruct the type and interval annotations on a species AST.
unerase :: USpeciesAST -> ESpeciesAST
unerase UZero                = wrap Zero
unerase UOne                 = wrap One
unerase (UN n)               = wrap (N n)
unerase UX                   = wrap X
unerase UE                   = wrap E
unerase UC                   = wrap C
unerase UL                   = wrap L
unerase USubset              = wrap Subset
unerase (UKSubset k)         = wrap (KSubset k)
unerase UElt                 = wrap Elt
unerase (f :+:% g)           = unerase f + unerase g
  where Wrap f + Wrap g      = wrap $ f :+: g
unerase (f :*:% g)           = unerase f * unerase g
  where Wrap f * Wrap g      = wrap $ f :*: g
unerase (f :.:% g)           = unerase f . unerase g
  where Wrap f . Wrap g      = wrap $ f :.: g
unerase (f :><:% g)          = unerase f >< unerase g
  where Wrap f >< Wrap g     = wrap $ f :><: g
unerase (f :@:% g)           = unerase f @@ unerase g
  where Wrap f @@ Wrap g     = wrap $ f :@: g
unerase (UDer f)             = der $ unerase f
  where der (Wrap f)         = wrap (Der f)
unerase (UOfSize f p)        = ofSize $ unerase f
  where ofSize (Wrap f)      = wrap $ OfSize f p
unerase (UOfSizeExactly f k) = ofSize $ unerase f
  where ofSize (Wrap f)      = wrap $ OfSizeExactly f k
unerase (UNonEmpty f)        = nonEmpty $ unerase f
  where nonEmpty (Wrap f)    = wrap $ NonEmpty f
unerase (URec f)             = wrap $ Rec f
unerase UOmega               = wrap Omega

-- | Substitute an expression for recursive occurrences.
substRec :: ASTFunctor f => f -> USpeciesAST -> USpeciesAST -> USpeciesAST
substRec c e (f :+:% g)                          = substRec c e f :+:% substRec c e g
substRec c e (f :*:% g)                          = substRec c e f :*:% substRec c e g
substRec c e (f :.:% g)                          = substRec c e f :.:% substRec c e g
substRec c e (f :><:% g)                         = substRec c e f :><:% substRec c e g
substRec c e (f :@:% g)                          = substRec c e f :@:% substRec c e g
substRec c e (UDer f)                            = UDer (substRec c e f)
substRec c e (UOfSize f p)                       = UOfSize (substRec c e f) p
substRec c e (UOfSizeExactly f k)                = UOfSizeExactly (substRec c e f) k
substRec c e (UNonEmpty f)                       = UNonEmpty (substRec c e f)
substRec c e (URec c')
  | (show . typeOf $ c) == (show . typeOf $ c')  = e
substRec _ _ f                                   = f