{-# LANGUAGE GADTs #-}

-- | Type class instances for 'TSpeciesAST', 'ESpeciesAST', and
--   'SpeciesAST', in a separate module to avoid a dependency cycle
--   between "Math.Combinatorics.Species.AST" and
--   "Math.Combinatorics.Species.Class".
module Math.Combinatorics.Species.AST.Instances
    ( reify, reflectT, reflectU, reflect )
    where

import NumericPrelude
import PreludeBase hiding (cycle)

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.AST
import Math.Combinatorics.Species.Util.Interval hiding (omega)
import qualified Math.Combinatorics.Species.Util.Interval as I

import qualified Algebra.Additive as Additive
import qualified Algebra.Ring as Ring
import qualified Algebra.Differential as Differential

import Data.Typeable

-- grr -- can't autoderive this because of URec constructor! =P
instance Eq SpeciesAST where
  UZero                == UZero                 = True
  UOne                 == UOne                  = True
  (UN m)               == (UN n)                = m == n
  UX                   == UX                    = True
  UE                   == UE                    = True
  UC                   == UC                    = True
  UL                   == UL                    = True
  USubset              == USubset               = True
  (UKSubset k)         == (UKSubset j)          = k == j
  UElt                 == UElt                  = True
  (f1 :+:% g1)         == (f2 :+:% g2)          = f1 == f2 && g1 == g2
  (f1 :*:% g1)         == (f2 :*:% g2)          = f1 == f2 && g1 == g2
  (f1 :.:% g1)         == (f2 :.:% g2)          = f1 == f2 && g1 == g2
  (f1 :><:% g1)        == (f2 :><:% g2)         = f1 == f2 && g1 == g2
  (f1 :@:% g1)         == (f2 :@:% g2)          = f1 == f2 && g1 == g2
  UDer f1              == UDer f2               = f1 == f2
  -- note, UOfSize will always compare False since we can't compare the functions for equality
  UOfSizeExactly f1 k1 == UOfSizeExactly f2 k2  = f1 == f2 && k1 == k2
  UNonEmpty f1         == UNonEmpty f2          = f1 == f2
  URec f1              == URec f2               = typeOf f1 == typeOf f2
  UOmega               == UOmega                = True
  _ == _                                        = False

instance Ord SpeciesAST where
  compare x y | x == y = EQ
  compare UZero _ = LT
  compare _ UZero = GT
  compare UOne _     = LT
  compare _ UOne     = GT
  compare (UN m) (UN n) = compare m n
  compare (UN _) _ = LT
  compare _ (UN _) = GT
  compare UX _ = LT
  compare _ UX = GT
  compare UE _ = LT
  compare _ UE = GT
  compare UC _ = LT
  compare _ UC = GT
  compare UL _ = LT
  compare _ UL = GT
  compare USubset _ = LT
  compare _ USubset = GT
  compare (UKSubset j) (UKSubset k) = compare j k
  compare (UKSubset _) _ = LT
  compare _ (UKSubset _) = GT
  compare UElt _ = LT
  compare _ UElt = GT
  compare (f1 :+:% g1) (f2 :+:% g2) | f1 == f2 = compare g1 g2
                                    | otherwise = compare f1 f2
  compare (_ :+:% _) _ = LT
  compare _ (_ :+:% _) = GT
  compare (f1 :*:% g1) (f2 :*:% g2) | f1 == f2 = compare g1 g2
                                    | otherwise = compare f1 f2
  compare (_ :*:% _) _ = LT
  compare _ (_ :*:% _) = GT
  compare (f1 :.:% g1) (f2 :.:% g2) | f1 == f2 = compare g1 g2
                                    | otherwise = compare f1 f2
  compare (_ :.:% _) _ = LT
  compare _ (_ :.:% _) = GT
  compare (f1 :><:% g1) (f2 :><:% g2) | f1 == f2 = compare g1 g2
                                      | otherwise = compare f1 f2
  compare (_ :><:% _) _ = LT
  compare _ (_ :><:% _) = GT
  compare (f1 :@:% g1) (f2 :@:% g2) | f1 == f2 = compare g1 g2
                                    | otherwise = compare f1 f2
  compare (_ :@:% _) _ = LT
  compare _ (_ :@:% _) = GT
  compare (UDer f1) (UDer f2) = compare f1 f2
  compare (UDer _) _ = LT
  compare _ (UDer _) = GT
  compare (UOfSize f1 p1) (UOfSize f2 p2) = compare f1 f2
  compare (UOfSize _ _) _ = LT
  compare _ (UOfSize _ _) = GT
  compare (UOfSizeExactly f1 k1) (UOfSizeExactly f2 k2)
    | f1 == f2 = compare k1 k2
    | otherwise = compare f1 f2
  compare (UOfSizeExactly _ _) _ = LT
  compare _ (UOfSizeExactly _ _) = GT
  compare (UNonEmpty f1) (UNonEmpty f2) = compare f1 f2
  compare (UNonEmpty _) _ = LT
  compare _ (UNonEmpty _) = GT
  compare (URec f1) (URec f2) = compare (show $ typeOf f1) (show $ typeOf f2)
  compare UOmega _ = LT
  compare _ UOmega = GT

instance Show SpeciesAST where
  showsPrec _ UZero                = shows (0 :: Int)
  showsPrec _ UOne                 = shows (1 :: Int)
  showsPrec _ (UN n)               = shows n
  showsPrec _ UX                   = showChar 'X'
  showsPrec _ UE                   = showChar 'E'
  showsPrec _ UC                   = showChar 'C'
  showsPrec _ UL                   = showChar 'L'
  showsPrec _ USubset              = showChar 'p'
  showsPrec _ (UKSubset n)         = showChar 'p' . shows n
  showsPrec _ (UElt)               = showChar 'e'
  showsPrec p (f :+:% g)           = showParen (p>6)  $ showsPrec 6 f
                                                     . showString " + "
                                                     . showsPrec 6 g
  showsPrec p (f :*:% g)           = showParen (p>=7) $ showsPrec 7 f
                                                     . showString " * "
                                                     . showsPrec 7 g
  showsPrec p (f :.:% g)           = showParen (p>=7) $ showsPrec 7 f
                                                     . showString " . "
                                                     . showsPrec 7 g
  showsPrec p (f :><:% g)          = showParen (p>=7) $ showsPrec 7 f
                                                     . showString " >< "
                                                     . showsPrec 7 g
  showsPrec p (f :@:% g)           = showParen (p>=7) $ showsPrec 7 f
                                                     . showString " @ "
                                                     . showsPrec 7 g
  showsPrec p (UDer f)             = showsPrec 11 f . showChar '\''
  showsPrec _ (UOfSize f p)        = showChar '<' .  showsPrec 0 f . showChar '>'
  showsPrec _ (UOfSizeExactly f n) = showsPrec 11 f . shows n
  showsPrec _ (UNonEmpty f)        = showsPrec 11 f . showChar '+'
  showsPrec _ (URec f)             = shows f

instance Additive.C SpeciesAST where
  zero   = UZero
  (+)    = (:+:%)
  negate = error "negation is not implemented yet!  wait until virtual species..."

instance Ring.C SpeciesAST where
  (*) = (:*:%)
  one = UOne
  fromInteger 0 = zero
  fromInteger 1 = one
  fromInteger n = UN n
  _ ^ 0 = one
  w ^ 1 = w
  f ^ n = f * (f ^ (n-1))

instance Differential.C SpeciesAST where
  differentiate = UDer

instance Species SpeciesAST where
  singleton     = UX
  set           = UE
  cycle         = UC
  linOrd        = UL
  subset        = USubset
  ksubset k     = UKSubset k
  element       = UElt
  o             = (:.:%)
  cartesian     = (:><:%)
  fcomp         = (:@:%)
  ofSize        = UOfSize
  ofSizeExactly = UOfSizeExactly
  nonEmpty      = UNonEmpty
  rec           = URec
  omega         = UOmega

instance Show (TSpeciesAST s) where
  show = show . erase'

instance Show ESpeciesAST where
  show = show . erase

instance Additive.C ESpeciesAST where
  zero   = wrap Zero
  Wrap f + Wrap g = wrap $ f :+: g
  negate = error "negation is not implemented yet!  wait until virtual species..."

instance Ring.C ESpeciesAST where
  Wrap f * Wrap g = wrap $ f :*: g
  one = wrap One
  fromInteger 0 = zero
  fromInteger 1 = one
  fromInteger n = wrap $ N n
  _ ^ 0 = one
  w@(Wrap{}) ^ 1 = w
  (Wrap f) ^ n   = case (Wrap f) ^ (n-1) of
                        (Wrap f') -> wrap $ f :*: f'

instance Differential.C ESpeciesAST where
  differentiate (Wrap f) = wrap (Der f)

instance Species ESpeciesAST where
  singleton                         = wrap X
  set                               = wrap E
  cycle                             = wrap C
  linOrd                            = wrap L
  subset                            = wrap Subset
  ksubset k                         = wrap $ KSubset k
  element                           = wrap Elt
  o (Wrap f) (Wrap g)               = wrap $ f :.: g
  cartesian (Wrap f) (Wrap g)       = wrap $ f :><: g
  fcomp (Wrap f) (Wrap g)           = wrap $ f :@: g
  ofSize (Wrap f) p                 = wrap $ OfSize f p
  ofSizeExactly (Wrap f) n          = wrap $ OfSizeExactly f n
  nonEmpty (Wrap f)                 = wrap $ NonEmpty f
  rec f                             = wrap $ Rec f
  omega                             = wrap Omega

-- | Reify a species expression into an AST.  Of course, this is just
--   the identity function with a usefully restricted type.  For
--   example:
--
-- > > reify octopus
-- > C . L+
-- > > reify (ksubset 3)
-- > E3 * E

reify :: ESpeciesAST -> ESpeciesAST
reify = id

-- | Reflect an AST back into any instance of the 'Species' class.
reflectU :: Species s => SpeciesAST -> s
reflectU UZero                = 0
reflectU UOne                 = 1
reflectU (UN n)               = fromInteger n
reflectU UX                   = singleton
reflectU UE                   = set
reflectU UC                   = cycle
reflectU UL                   = linOrd
reflectU USubset              = subset
reflectU (UKSubset k)         = ksubset k
reflectU UElt                 = element
reflectU (f :+:% g)           = reflectU f + reflectU g
reflectU (f :*:% g)           = reflectU f * reflectU g
reflectU (f :.:% g)           = reflectU f `o` reflectU g
reflectU (f :><:% g)          = reflectU f >< reflectU g
reflectU (f :@:% g)           = reflectU f @@ reflectU g
reflectU (UDer f)             = oneHole (reflectU f)
reflectU (UOfSize f p)        = ofSize (reflectU f) p
reflectU (UOfSizeExactly f n) = ofSizeExactly (reflectU f) n
reflectU (UNonEmpty f)        = nonEmpty (reflectU f)
reflectU (URec f)             = rec f
reflectU UOmega               = omega

reflectT :: Species s => TSpeciesAST f -> s
reflectT = reflectU . erase'

-- | Reflect an AST back into any instance of the 'Species' class.
reflect :: Species s => ESpeciesAST -> s
reflect = reflectU . erase
