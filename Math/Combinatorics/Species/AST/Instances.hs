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

-- grr -- can't autoderive this because of Rec constructor! =P
instance Eq SpeciesAST where
  Zero                == Zero                 = True
  One                 == One                  = True
  (N m)               == (N n)                = m == n
  X                   == X                    = True
  E                   == E                    = True
  C                   == C                    = True
  L                   == L                    = True
  Subset              == Subset               = True
  (KSubset k)         == (KSubset j)          = k == j
  Elt                 == Elt                  = True
  (f1 :+: g1)         == (f2 :+: g2)          = f1 == f2 && g1 == g2
  (f1 :*: g1)         == (f2 :*: g2)          = f1 == f2 && g1 == g2
  (f1 :.: g1)         == (f2 :.: g2)          = f1 == f2 && g1 == g2
  (f1 :><: g1)        == (f2 :><: g2)         = f1 == f2 && g1 == g2
  (f1 :@: g1)         == (f2 :@: g2)          = f1 == f2 && g1 == g2
  Der f1              == Der f2               = f1 == f2
  -- note, OfSize will always compare False since we can't compare the functions for equality
  OfSizeExactly f1 k1 == OfSizeExactly f2 k2  = f1 == f2 && k1 == k2
  NonEmpty f1         == NonEmpty f2          = f1 == f2
  Rec f1              == Rec f2               = typeOf f1 == typeOf f2
  Omega               == Omega                = True
  _ == _                                        = False

instance Ord SpeciesAST where
  compare x y | x == y = EQ
  compare Zero _ = LT
  compare _ Zero = GT
  compare One _     = LT
  compare _ One     = GT
  compare (N m) (N n) = compare m n
  compare (N _) _ = LT
  compare _ (N _) = GT
  compare X _ = LT
  compare _ X = GT
  compare E _ = LT
  compare _ E = GT
  compare C _ = LT
  compare _ C = GT
  compare L _ = LT
  compare _ L = GT
  compare Subset _ = LT
  compare _ Subset = GT
  compare (KSubset j) (KSubset k) = compare j k
  compare (KSubset _) _ = LT
  compare _ (KSubset _) = GT
  compare Elt _ = LT
  compare _ Elt = GT
  compare (f1 :+: g1) (f2 :+: g2) | f1 == f2 = compare g1 g2
                                    | otherwise = compare f1 f2
  compare (_ :+: _) _ = LT
  compare _ (_ :+: _) = GT
  compare (f1 :*: g1) (f2 :*: g2) | f1 == f2 = compare g1 g2
                                    | otherwise = compare f1 f2
  compare (_ :*: _) _ = LT
  compare _ (_ :*: _) = GT
  compare (f1 :.: g1) (f2 :.: g2) | f1 == f2 = compare g1 g2
                                    | otherwise = compare f1 f2
  compare (_ :.: _) _ = LT
  compare _ (_ :.: _) = GT
  compare (f1 :><: g1) (f2 :><: g2) | f1 == f2 = compare g1 g2
                                      | otherwise = compare f1 f2
  compare (_ :><: _) _ = LT
  compare _ (_ :><: _) = GT
  compare (f1 :@: g1) (f2 :@: g2) | f1 == f2 = compare g1 g2
                                    | otherwise = compare f1 f2
  compare (_ :@: _) _ = LT
  compare _ (_ :@: _) = GT
  compare (Der f1) (Der f2) = compare f1 f2
  compare (Der _) _ = LT
  compare _ (Der _) = GT
  compare (OfSize f1 p1) (OfSize f2 p2) = compare f1 f2
  compare (OfSize _ _) _ = LT
  compare _ (OfSize _ _) = GT
  compare (OfSizeExactly f1 k1) (OfSizeExactly f2 k2)
    | f1 == f2 = compare k1 k2
    | otherwise = compare f1 f2
  compare (OfSizeExactly _ _) _ = LT
  compare _ (OfSizeExactly _ _) = GT
  compare (NonEmpty f1) (NonEmpty f2) = compare f1 f2
  compare (NonEmpty _) _ = LT
  compare _ (NonEmpty _) = GT
  compare (Rec f1) (Rec f2) = compare (show $ typeOf f1) (show $ typeOf f2)
  compare Omega _ = LT
  compare _ Omega = GT

instance Show SpeciesAST where
  showsPrec _ Zero                = shows (0 :: Int)
  showsPrec _ One                 = shows (1 :: Int)
  showsPrec _ (N n)               = shows n
  showsPrec _ X                   = showChar 'X'
  showsPrec _ E                   = showChar 'E'
  showsPrec _ C                   = showChar 'C'
  showsPrec _ L                   = showChar 'L'
  showsPrec _ Subset              = showChar 'p'
  showsPrec _ (KSubset n)         = showChar 'p' . shows n
  showsPrec _ (Elt)               = showChar 'e'
  showsPrec p (f :+: g)           = showParen (p>6)  $ showsPrec 6 f
                                                     . showString " + "
                                                     . showsPrec 6 g
  showsPrec p (f :*: g)           = showParen (p>=7) $ showsPrec 7 f
                                                     . showString " * "
                                                     . showsPrec 7 g
  showsPrec p (f :.: g)           = showParen (p>=7) $ showsPrec 7 f
                                                     . showString " . "
                                                     . showsPrec 7 g
  showsPrec p (f :><: g)          = showParen (p>=7) $ showsPrec 7 f
                                                     . showString " >< "
                                                     . showsPrec 7 g
  showsPrec p (f :@: g)           = showParen (p>=7) $ showsPrec 7 f
                                                     . showString " @ "
                                                     . showsPrec 7 g
  showsPrec p (Der f)             = showsPrec 11 f . showChar '\''
  showsPrec _ (OfSize f p)        = showChar '<' .  showsPrec 0 f . showChar '>'
  showsPrec _ (OfSizeExactly f n) = showsPrec 11 f . shows n
  showsPrec _ (NonEmpty f)        = showsPrec 11 f . showChar '+'
  showsPrec _ (Rec f)             = shows f

instance Additive.C SpeciesAST where
  zero   = Zero
  (+)    = (:+:)
  negate = error "negation is not implemented yet!  wait until virtual species..."

instance Ring.C SpeciesAST where
  (*) = (:*:)
  one = One
  fromInteger 0 = zero
  fromInteger 1 = one
  fromInteger n = N n
  _ ^ 0 = one
  w ^ 1 = w
  f ^ n = f * (f ^ (n-1))

instance Differential.C SpeciesAST where
  differentiate = Der

instance Species SpeciesAST where
  singleton     = X
  set           = E
  cycle         = C
  linOrd        = L
  subset        = Subset
  ksubset k     = KSubset k
  element       = Elt
  o             = (:.:)
  cartesian     = (:><:)
  fcomp         = (:@:)
  ofSize        = OfSize
  ofSizeExactly = OfSizeExactly
  nonEmpty      = NonEmpty
  rec           = Rec
  omega         = Omega

instance Show (TSpeciesAST s) where
  show = show . erase'

instance Show ESpeciesAST where
  show = show . erase

instance Additive.C ESpeciesAST where
  zero   = wrap TZero
  Wrap f + Wrap g = wrap $ f :+:: g
  negate = error "negation is not implemented yet!  wait until virtual species..."

instance Ring.C ESpeciesAST where
  Wrap f * Wrap g = wrap $ f :*:: g
  one = wrap TOne
  fromInteger 0 = zero
  fromInteger 1 = one
  fromInteger n = wrap $ TN n
  _ ^ 0 = one
  w@(Wrap{}) ^ 1 = w
  (Wrap f) ^ n   = case (Wrap f) ^ (n-1) of
                        (Wrap f') -> wrap $ f :*:: f'

instance Differential.C ESpeciesAST where
  differentiate (Wrap f) = wrap (TDer f)

instance Species ESpeciesAST where
  singleton                         = wrap TX
  set                               = wrap TE
  cycle                             = wrap TC
  linOrd                            = wrap TL
  subset                            = wrap TSubset
  ksubset k                         = wrap $ TKSubset k
  element                           = wrap TElt
  o (Wrap f) (Wrap g)               = wrap $ f :.:: g
  cartesian (Wrap f) (Wrap g)       = wrap $ f :><:: g
  fcomp (Wrap f) (Wrap g)           = wrap $ f :@:: g
  ofSize (Wrap f) p                 = wrap $ TOfSize f p
  ofSizeExactly (Wrap f) n          = wrap $ TOfSizeExactly f n
  nonEmpty (Wrap f)                 = wrap $ TNonEmpty f
  rec f                             = wrap $ TRec f
  omega                             = wrap TOmega

-- | Reify a species expression into an AST.  Of course, this is just
--   the identity function with a usefully restricted type.  For
--   example:
--
-- > > reify octopus
-- > C . TL+
-- > > reify (ksubset 3)
-- > E3 * TE

reify :: ESpeciesAST -> ESpeciesAST
reify = id

-- | Reflect an AST back into any instance of the 'Species' class.
reflectU :: Species s => SpeciesAST -> s
reflectU Zero                = 0
reflectU One                 = 1
reflectU (N n)               = fromInteger n
reflectU X                   = singleton
reflectU E                   = set
reflectU C                   = cycle
reflectU L                   = linOrd
reflectU Subset              = subset
reflectU (KSubset k)         = ksubset k
reflectU Elt                 = element
reflectU (f :+: g)           = reflectU f + reflectU g
reflectU (f :*: g)           = reflectU f * reflectU g
reflectU (f :.: g)           = reflectU f `o` reflectU g
reflectU (f :><: g)          = reflectU f >< reflectU g
reflectU (f :@: g)           = reflectU f @@ reflectU g
reflectU (Der f)             = oneHole (reflectU f)
reflectU (OfSize f p)        = ofSize (reflectU f) p
reflectU (OfSizeExactly f n) = ofSizeExactly (reflectU f) n
reflectU (NonEmpty f)        = nonEmpty (reflectU f)
reflectU (Rec f)             = rec f
reflectU Omega               = omega

reflectT :: Species s => TSpeciesAST f -> s
reflectT = reflectU . erase'

-- | Reflect an AST back into any instance of the 'Species' class.
reflect :: Species s => ESpeciesAST -> s
reflect = reflectU . erase
