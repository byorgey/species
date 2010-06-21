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
   TC        :: TSpeciesAST Cycle
   TL        :: TSpeciesAST []
   TSubset   :: TSpeciesAST Set
   TKSubset  :: Integer -> TSpeciesAST Set
   TElt      :: TSpeciesAST Id
   (:+::)    :: SizedSpeciesAST f -> SizedSpeciesAST g -> TSpeciesAST (Sum f g)
   (:*::)    :: SizedSpeciesAST f -> SizedSpeciesAST g -> TSpeciesAST (Prod f g)
   (:.::)    :: SizedSpeciesAST f -> SizedSpeciesAST g -> TSpeciesAST (Comp f g)
   (:><::)   :: SizedSpeciesAST f -> SizedSpeciesAST g -> TSpeciesAST (Prod f g)
   (:@::)    :: SizedSpeciesAST f -> SizedSpeciesAST g -> TSpeciesAST (Comp f g)
   TDer      :: SizedSpeciesAST f -> TSpeciesAST (Comp f Star)
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
interval TOne                 = 0
interval (TN n)               = 0
interval TX                   = 1
interval TE                   = natsI
interval TC                   = fromI 1
interval TL                   = natsI
interval TSubset              = natsI
interval (TKSubset k)         = fromI (fromInteger k)
interval TElt                 = fromI 1
interval (f :+:: g)           = getI f `I.union` getI g
interval (f :*:: g)           = getI f + getI g
interval (f :.:: g)           = getI f * getI g
interval (f :><:: g)          = getI f `I.intersect` getI g
interval (f :@:: g)           = natsI
    -- Note, the above interval for functor composition is obviously
    -- overly conservative.  To do this right we'd have to compute the
    -- generating function for g --- and actually it would depend on
    -- whether we were doing labelled or unlabelled enumeration, which
    -- we don't know at this point.
interval (TDer f)             = decrI (getI f)
interval (TOfSize f p)        = fromI $ smallestIn (getI f) p
interval (TOfSizeExactly f n) = fromInteger n `I.intersect` getI f
interval (TNonEmpty f)        = fromI 1 `I.intersect` getI f
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
needsZ L            = True
needsZ (f :+:% g)    = needsZ f || needsZ g
needsZ (f :*:% g)    = needsZ f || needsZ g
needsZ (_ :.:% _)    = True
needsZ (_ :><:% _)   = True
needsZ (_ :@:% _)    = True
needsZ (Der _)      = True
needsZ (OfSize f _) = needsZ f
needsZ (OfSizeExactly f _) = needsZ f
needsZ (NonEmpty f) = needsZ f
needsZ (Rec _)      = True    -- Newton-Raphson iteration uses composition
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
  (:+:%)         :: SpeciesAST -> SpeciesAST -> SpeciesAST
  (:*:%)         :: SpeciesAST -> SpeciesAST -> SpeciesAST
  (:.:%)         :: SpeciesAST -> SpeciesAST -> SpeciesAST
  (:><:%)        :: SpeciesAST -> SpeciesAST -> SpeciesAST
  (:@:%)         :: SpeciesAST -> SpeciesAST -> SpeciesAST
  Der           :: SpeciesAST -> SpeciesAST
  OfSize        :: SpeciesAST -> (Integer -> Bool) -> SpeciesAST
  OfSizeExactly :: SpeciesAST -> Integer -> SpeciesAST
  NonEmpty      :: SpeciesAST -> SpeciesAST
  Rec           :: ASTFunctor f => f -> SpeciesAST
  Omega         :: SpeciesAST

-- | Erase the type and interval information from a species AST.
erase :: ESpeciesAST -> SpeciesAST
erase (Wrap s) = erase' (stripI s)

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
erase' (f :+:: g)           = erase' (stripI f) :+:% erase' (stripI g)
erase' (f :*:: g)           = erase' (stripI f) :*:% erase' (stripI g)
erase' (f :.:: g)           = erase' (stripI f) :.:% erase' (stripI g)
erase' (f :><:: g)          = erase' (stripI f) :><:% erase' (stripI g)
erase' (f :@:: g)           = erase' (stripI f) :@:% erase' (stripI g)
erase' (TDer f)             = Der . erase' . stripI $ f
erase' (TOfSize f p)        = OfSize (erase' . stripI $ f) p
erase' (TOfSizeExactly f k) = OfSizeExactly (erase' . stripI $ f) k
erase' (TNonEmpty f)        = NonEmpty . erase' . stripI $ f
erase' (TRec f)             = Rec f
erase' TOmega               = Omega

-- | Reconstruct the type and interval annotations on a species AST.
unerase :: SpeciesAST -> ESpeciesAST
unerase Zero                = wrap TZero
unerase One                 = wrap TOne
unerase (N n)               = wrap (TN n)
unerase X                   = wrap TX
unerase E                   = wrap TE
unerase C                   = wrap TC
unerase L                   = wrap TL
unerase Subset              = wrap TSubset
unerase (KSubset k)         = wrap (TKSubset k)
unerase Elt                 = wrap TElt
unerase (f :+:% g)           = unerase f + unerase g
  where Wrap f + Wrap g      = wrap $ f :+:: g
unerase (f :*:% g)           = unerase f * unerase g
  where Wrap f * Wrap g      = wrap $ f :*:: g
unerase (f :.:% g)           = unerase f . unerase g
  where Wrap f . Wrap g      = wrap $ f :.:: g
unerase (f :><:% g)          = unerase f >< unerase g
  where Wrap f >< Wrap g     = wrap $ f :><:: g
unerase (f :@:% g)           = unerase f @@ unerase g
  where Wrap f @@ Wrap g     = wrap $ f :@:: g
unerase (Der f)             = der $ unerase f
  where der (Wrap f)         = wrap (TDer f)
unerase (OfSize f p)        = ofSize $ unerase f
  where ofSize (Wrap f)      = wrap $ TOfSize f p
unerase (OfSizeExactly f k) = ofSize $ unerase f
  where ofSize (Wrap f)      = wrap $ TOfSizeExactly f k
unerase (NonEmpty f)        = nonEmpty $ unerase f
  where nonEmpty (Wrap f)    = wrap $ TNonEmpty f
unerase (Rec f)             = wrap $ TRec f
unerase Omega               = wrap TOmega

-- | Substitute an expression for recursive occurrences.
substRec :: ASTFunctor f => f -> SpeciesAST -> SpeciesAST -> SpeciesAST
substRec c e (f :+:% g)                          = substRec c e f :+:% substRec c e g
substRec c e (f :*:% g)                          = substRec c e f :*:% substRec c e g
substRec c e (f :.:% g)                          = substRec c e f :.:% substRec c e g
substRec c e (f :><:% g)                         = substRec c e f :><:% substRec c e g
substRec c e (f :@:% g)                          = substRec c e f :@:% substRec c e g
substRec c e (Der f)                            = Der (substRec c e f)
substRec c e (OfSize f p)                       = OfSize (substRec c e f) p
substRec c e (OfSizeExactly f k)                = OfSizeExactly (substRec c e f) k
substRec c e (NonEmpty f)                       = NonEmpty (substRec c e f)
substRec c e (Rec c')
  | (show . typeOf $ c) == (show . typeOf $ c')  = e
substRec _ _ f                                   = f