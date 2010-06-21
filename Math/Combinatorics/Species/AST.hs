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
      TSpeciesAST(..), SizedSpeciesAST(..)
    , interval, annI, getI, stripI
    , ESpeciesAST(..), wrap, unwrap
    , ASTFunctor(..)

    , needsZ, needsZE

    , SpeciesAST(..), erase, erase', unerase
    , substRec

    ) where

import Math.Combinatorics.Species.Structures
import Math.Combinatorics.Species.Util.Interval
import qualified Math.Combinatorics.Species.Util.Interval as I

import Data.Typeable
import Unsafe.Coerce

import Data.Maybe (fromMaybe)

import NumericPrelude
import PreludeBase hiding (cycle)

-- | Reified combinatorial species.  Note that 'TSpeciesAST' has a
--   phantom type parameter which also reflects the structure, so we
--   can write quasi-dependently-typed functions over species, in
--   particular for species enumeration.
--
--   Of course, the non-uniform type parameter means that
--   'TSpeciesAST' cannot be an instance of the 'Species' class;
--   for that purpose the existential wrapper 'ESpeciesAST' is
--   provided.
--
--   'TSpeciesAST' is defined via mutual recursion with
--   'SizedSpeciesAST', which pairs a 'TSpeciesAST' with an interval
--   annotation indicating (a conservative approximation of) the label
--   set sizes for which the species actually yields any structures.
--   A value of 'SizedSpeciesAST' is thus an annotated species
--   expression tree with interval annotations at every node.
data TSpeciesAST (s :: * -> *) where
   TZero     :: TSpeciesAST Void
   TOne      :: TSpeciesAST Unit
   TN        :: Integer -> TSpeciesAST (Const Integer)
   TX        :: TSpeciesAST Id
   TE        :: TSpeciesAST Set
   C        :: TSpeciesAST Cycle
   TL        :: TSpeciesAST []
   TSubset   :: TSpeciesAST Set
   TKSubset  :: Integer -> TSpeciesAST Set
   TElt      :: TSpeciesAST Id
   (:+:)    :: SizedSpeciesAST f -> SizedSpeciesAST g -> TSpeciesAST (Sum f g)
   (:*:)    :: SizedSpeciesAST f -> SizedSpeciesAST g -> TSpeciesAST (Prod f g)
   (:.:)    :: SizedSpeciesAST f -> SizedSpeciesAST g -> TSpeciesAST (Comp f g)
   (:><:)   :: SizedSpeciesAST f -> SizedSpeciesAST g -> TSpeciesAST (Prod f g)
   (:@:)    :: SizedSpeciesAST f -> SizedSpeciesAST g -> TSpeciesAST (Comp f g)
   TDer      :: SizedSpeciesAST f -> TSpeciesAST (Comp f Star)
   TOfSize   :: SizedSpeciesAST f -> (Integer -> Bool) -> TSpeciesAST f
   TOfSizeExactly :: SizedSpeciesAST f -> Integer -> TSpeciesAST f
   TNonEmpty :: SizedSpeciesAST f -> TSpeciesAST f
   TRec      :: ASTFunctor f => f -> TSpeciesAST (Mu f)

   Omega    :: TSpeciesAST Void

data SizedSpeciesAST (s :: * -> *) where
  Sized :: Interval -> TSpeciesAST s -> SizedSpeciesAST s

-- | Given a 'TSpeciesAST', compute (a conservative approximation of)
--   the interval of label set sizes on which the species yields any
--   structures.
interval :: TSpeciesAST s -> Interval
interval TZero                = emptyI
interval TOne                 = 0
interval (TN n)               = 0
interval TX                   = 1
interval TE                   = natsI
interval C                   = fromI 1
interval TL                   = natsI
interval TSubset              = natsI
interval (TKSubset k)         = fromI (fromInteger k)
interval TElt                 = fromI 1
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
interval (TDer f)             = decrI (getI f)
interval (TOfSize f p)        = fromI $ smallestIn (getI f) p
interval (TOfSizeExactly f n) = fromInteger n `I.intersect` getI f
interval (TNonEmpty f)        = fromI 1 `I.intersect` getI f
interval (TRec f)             = interval (apply f Omega)
interval Omega               = omegaI

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

-- | Retrieve the interval annotation.
getI :: SizedSpeciesAST s -> Interval
getI (Sized i _) = i

-- | Type class for codes which can be interpreted as higher-order
--   functors.
class (Typeable f, Show f, Typeable1 (Interp f (Mu f))) => ASTFunctor f where
  apply :: Typeable1 g => f -> TSpeciesAST g -> TSpeciesAST (Interp f g)

-- | 'needsZ' is a predicate which checks whether a species uses any
--   of the operations which are not supported directly by ordinary
--   generating functions (composition, differentiation, cartesian
--   product, and functor composition), and hence need cycle index
--   series.
needsZ :: SpeciesAST -> Bool
needsZ UL            = True
needsZ (f :+:% g)    = needsZ f || needsZ g
needsZ (f :*:% g)    = needsZ f || needsZ g
needsZ (_ :.:% _)    = True
needsZ (_ :><:% _)   = True
needsZ (_ :@:% _)    = True
needsZ (UDer _)      = True
needsZ (UOfSize f _) = needsZ f
needsZ (UOfSizeExactly f _) = needsZ f
needsZ (UNonEmpty f) = needsZ f
needsZ (URec _)      = True    -- Newton-Raphson iteration uses composition
needsZ _             = False

-- | An existential wrapper to hide the phantom type parameter to
--   'SizedSpeciesAST', so we can make it an instance of 'Species'.
data ESpeciesAST where
  Wrap :: Typeable1 s => SizedSpeciesAST s -> ESpeciesAST

-- | Smart wrap constructor which also adds an appropriate interval
--   annotation.
wrap :: Typeable1 s => TSpeciesAST s -> ESpeciesAST
wrap = Wrap . annI

-- | Unwrap the existential wrapper and get out a typed AST.  You can
--   get out any type you like as long as it is the right one.
--
--   CAUTION: Don't try this at home.
unwrap :: Typeable1 s => ESpeciesAST -> TSpeciesAST s
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

-- | A version of 'needsZ' for 'ESpeciesAST'.
needsZE :: ESpeciesAST -> Bool
needsZE = needsZ . erase

-- | A plain old untyped variant of the species AST, for more easily
--   doing things like analysis, simplification, deriving
--   isomorphisms, and so on.  Converting between 'ESpeciesAST' and
--   'SpeciesAST' can be done with 'erase' and 'unerase'.
data SpeciesAST where
  UZero          :: SpeciesAST
  UOne           :: SpeciesAST
  UN             :: Integer -> SpeciesAST
  UX             :: SpeciesAST
  UE             :: SpeciesAST
  UC             :: SpeciesAST
  UL             :: SpeciesAST
  USubset        :: SpeciesAST
  UKSubset       :: Integer -> SpeciesAST
  UElt           :: SpeciesAST
  (:+:%)         :: SpeciesAST -> SpeciesAST -> SpeciesAST
  (:*:%)         :: SpeciesAST -> SpeciesAST -> SpeciesAST
  (:.:%)         :: SpeciesAST -> SpeciesAST -> SpeciesAST
  (:><:%)        :: SpeciesAST -> SpeciesAST -> SpeciesAST
  (:@:%)         :: SpeciesAST -> SpeciesAST -> SpeciesAST
  UDer           :: SpeciesAST -> SpeciesAST
  UOfSize        :: SpeciesAST -> (Integer -> Bool) -> SpeciesAST
  UOfSizeExactly :: SpeciesAST -> Integer -> SpeciesAST
  UNonEmpty      :: SpeciesAST -> SpeciesAST
  URec           :: ASTFunctor f => f -> SpeciesAST
  UOmega         :: SpeciesAST

-- | Erase the type and interval information from a species AST.
erase :: ESpeciesAST -> SpeciesAST
erase (Wrap s) = erase' (stripI s)

erase' :: TSpeciesAST f -> SpeciesAST
erase' TZero                = UZero
erase' TOne                 = UOne
erase' (TN n)               = UN n
erase' TX                   = UX
erase' TE                   = UE
erase' C                   = UC
erase' TL                   = UL
erase' TSubset              = USubset
erase' (TKSubset k)         = UKSubset k
erase' TElt                 = UElt
erase' (f :+: g)           = erase' (stripI f) :+:% erase' (stripI g)
erase' (f :*: g)           = erase' (stripI f) :*:% erase' (stripI g)
erase' (f :.: g)           = erase' (stripI f) :.:% erase' (stripI g)
erase' (f :><: g)          = erase' (stripI f) :><:% erase' (stripI g)
erase' (f :@: g)           = erase' (stripI f) :@:% erase' (stripI g)
erase' (TDer f)             = UDer . erase' . stripI $ f
erase' (TOfSize f p)        = UOfSize (erase' . stripI $ f) p
erase' (TOfSizeExactly f k) = UOfSizeExactly (erase' . stripI $ f) k
erase' (TNonEmpty f)        = UNonEmpty . erase' . stripI $ f
erase' (TRec f)             = URec f
erase' Omega               = UOmega

-- | Reconstruct the type and interval annotations on a species AST.
unerase :: SpeciesAST -> ESpeciesAST
unerase UZero                = wrap TZero
unerase UOne                 = wrap TOne
unerase (UN n)               = wrap (TN n)
unerase UX                   = wrap TX
unerase UE                   = wrap TE
unerase UC                   = wrap C
unerase UL                   = wrap TL
unerase USubset              = wrap TSubset
unerase (UKSubset k)         = wrap (TKSubset k)
unerase UElt                 = wrap TElt
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
  where der (Wrap f)         = wrap (TDer f)
unerase (UOfSize f p)        = ofSize $ unerase f
  where ofSize (Wrap f)      = wrap $ TOfSize f p
unerase (UOfSizeExactly f k) = ofSize $ unerase f
  where ofSize (Wrap f)      = wrap $ TOfSizeExactly f k
unerase (UNonEmpty f)        = nonEmpty $ unerase f
  where nonEmpty (Wrap f)    = wrap $ TNonEmpty f
unerase (URec f)             = wrap $ TRec f
unerase UOmega               = wrap Omega

-- | Substitute an expression for recursive occurrences.
substRec :: ASTFunctor f => f -> SpeciesAST -> SpeciesAST -> SpeciesAST
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