{-# LANGUAGE CPP, GADTs #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Math.Combinatorics.Species.AST.Instances
-- Copyright   :  (c) Brent Yorgey 2010
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@cis.upenn.edu
-- Stability   :  experimental
--
-- Type class instances for 'TSpeciesAST', 'ESpeciesAST', and
-- 'SpeciesAST', in a separate module to avoid a dependency cycle
-- between "Math.Combinatorics.Species.AST" and
-- "Math.Combinatorics.Species.Class".
--
-- This module also contains functions for reifying species
-- expressions to ASTs and reflecting ASTs back into other species
-- instances, which are in this module since they depend on the AST
-- type class instances.
--
-----------------------------------------------------------------------------

module Math.Combinatorics.Species.AST.Instances
    ( reify, reifyE, reflect, reflectT, reflectE )
    where

#if MIN_VERSION_numeric_prelude(0,2,0)
import NumericPrelude hiding (cycle)
#else
import NumericPrelude
import PreludeBase hiding (cycle)
#endif

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.AST
import Math.Combinatorics.Species.Util.Interval hiding (omega)
import qualified Math.Combinatorics.Species.Util.Interval as I

import qualified Algebra.Additive as Additive
import qualified Algebra.Ring as Ring
import qualified Algebra.Differential as Differential

import Data.Typeable

------------------------------------------------------------
--  SpeciesAST instances  ----------------------------------
------------------------------------------------------------

-- grr -- can't autoderive this because of Rec constructor! =P

-- | Species expressions can be compared for /structural/ equality.
--   (Note that if @s1@ and @s2@ are /isomorphic/ species we do not
--   necessarily have @s1 == s2@.)
--
--   Note, however, that species containing an 'OfSize' constructor
--   will always compare as @False@ with any other species, since we
--   cannot decide function equality.
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
  (f1 :+ g1)         == (f2 :+ g2)          = f1 == f2 && g1 == g2
  (f1 :* g1)         == (f2 :* g2)          = f1 == f2 && g1 == g2
  (f1 :. g1)         == (f2 :. g2)          = f1 == f2 && g1 == g2
  (f1 :>< g1)        == (f2 :>< g2)         = f1 == f2 && g1 == g2
  (f1 :@ g1)         == (f2 :@ g2)          = f1 == f2 && g1 == g2
  Der f1              == Der f2               = f1 == f2
  -- note, OfSize will always compare False since we can't compare the functions for equality
  OfSizeExactly f1 k1 == OfSizeExactly f2 k2  = f1 == f2 && k1 == k2
  NonEmpty f1         == NonEmpty f2          = f1 == f2
  Rec f1              == Rec f2               = typeOf f1 == typeOf f2
  Omega               == Omega                = True
  _ == _                                      = False


-- argh, can't derive this either.  ugh.
-- | An (arbitrary) 'Ord' instance, so that we can put species
--   expressions in canonical order when simplifying.
instance Ord SpeciesAST where
  compare x y  | x == y             = EQ
  compare Zero _                    = LT
  compare _ Zero                    = GT
  compare One _                     = LT
  compare _ One                     = GT
  compare (N m) (N n)               = compare m n
  compare (N _) _                   = LT
  compare _ (N _)                   = GT
  compare X _                       = LT
  compare _ X                       = GT
  compare E _                       = LT
  compare _ E                       = GT
  compare C _                       = LT
  compare _ C                       = GT
  compare L _                       = LT
  compare _ L                       = GT
  compare Subset _                  = LT
  compare _ Subset                  = GT
  compare (KSubset j) (KSubset k)   = compare j k
  compare (KSubset _) _             = LT
  compare _ (KSubset _)             = GT
  compare Elt _                     = LT
  compare _ Elt                     = GT
  compare (f1 :+ g1) (f2 :+ g2)   | f1 == f2  = compare g1 g2
                                    | otherwise = compare f1 f2
  compare (_ :+ _) _               = LT
  compare _ (_ :+ _)               = GT
  compare (f1 :* g1) (f2 :* g2)   | f1 == f2  = compare g1 g2
                                    | otherwise = compare f1 f2
  compare (_ :* _) _               = LT
  compare _ (_ :* _)               = GT
  compare (f1 :. g1) (f2 :. g2)   | f1 == f2  = compare g1 g2
                                    | otherwise = compare f1 f2
  compare (_ :. _) _               = LT
  compare _ (_ :. _)               = GT
  compare (f1 :>< g1) (f2 :>< g2) | f1 == f2  = compare g1 g2
                                    | otherwise = compare f1 f2
  compare (_ :>< _) _              = LT
  compare _ (_ :>< _)              = GT
  compare (f1 :@ g1) (f2 :@ g2)   | f1 == f2  = compare g1 g2
                                    | otherwise = compare f1 f2
  compare (_ :@ _) _               = LT
  compare _ (_ :@ _)               = GT
  compare (Der f1) (Der f2)         = compare f1 f2
  compare (Der _) _                 = LT
  compare _ (Der _)                 = GT
  compare (OfSize f1 p1) (OfSize f2 p2)
                                    = compare f1 f2
  compare (OfSize _ _) _            = LT
  compare _ (OfSize _ _)            = GT
  compare (OfSizeExactly f1 k1) (OfSizeExactly f2 k2)
                                    | f1 == f2  = compare k1 k2
                                    | otherwise = compare f1 f2
  compare (OfSizeExactly _ _) _     = LT
  compare _ (OfSizeExactly _ _)     = GT
  compare (NonEmpty f1) (NonEmpty f2)
                                    = compare f1 f2
  compare (NonEmpty _) _            = LT
  compare _ (NonEmpty _)            = GT
  compare (Rec f1) (Rec f2)         = compare (show $ typeOf f1) (show $ typeOf f2)
  compare Omega _                   = LT
  compare _ Omega                   = GT

-- | Display species expressions in a nice human-readable form.  Note
--   that we commit the unforgivable sin of omitting a corresponding
--   Read instance.  This will hopefully be remedied in a future
--   version.
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
  showsPrec p (f :+ g)           = showParen (p>6)  $ showsPrec 6 f
                                                     . showString " + "
                                                     . showsPrec 6 g
  showsPrec p (f :* g)           = showParen (p>=7) $ showsPrec 7 f
                                                     . showString " * "
                                                     . showsPrec 7 g
  showsPrec p (f :. g)           = showParen (p>=7) $ showsPrec 7 f
                                                     . showString " . "
                                                     . showsPrec 7 g
  showsPrec p (f :>< g)          = showParen (p>=7) $ showsPrec 7 f
                                                     . showString " >< "
                                                     . showsPrec 7 g
  showsPrec p (f :@ g)           = showParen (p>=7) $ showsPrec 7 f
                                                     . showString " @ "
                                                     . showsPrec 7 g
  showsPrec p (Der f)             = showsPrec 11 f . showChar '\''
  showsPrec _ (OfSize f p)        = showChar '<' .  showsPrec 0 f . showChar '>'
  showsPrec _ (OfSizeExactly f n) = showsPrec 11 f . shows n
  showsPrec _ (NonEmpty f)        = showsPrec 11 f . showChar '+'
  showsPrec _ (Rec f)             = shows f

-- | Species expressions are additive.
instance Additive.C SpeciesAST where
  zero   = Zero
  (+)    = (:+)
  negate = error "negation is not implemented yet!  wait until virtual species..."

-- | Species expressions form a ring.  Well, sort of.  Of course the
--   ring laws actually only hold up to isomorphism of species, not up
--   to structural equality.
instance Ring.C SpeciesAST where
  (*) = (:*)
  one = One
  fromInteger 0 = zero
  fromInteger 1 = one
  fromInteger n = N n
  _ ^ 0 = one
  w ^ 1 = w
  f ^ n = f * (f ^ (n-1))

-- | Species expressions are differentiable.
instance Differential.C SpeciesAST where
  differentiate = Der

-- | Species expressions are an instance of the 'Species' class, so we
--   can use the Species class DSL to build species expression ASTs.
instance Species SpeciesAST where
  singleton     = X
  set           = E
  cycle         = C
  linOrd        = L
  subset        = Subset
  ksubset k     = KSubset k
  element       = Elt
  o             = (:.)
  (><)          = (:><)
  (@@)          = (:@)
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
  singleton                 = wrap TX
  set                       = wrap TE
  cycle                     = wrap TC
  linOrd                    = wrap TL
  subset                    = wrap TSubset
  ksubset k                 = wrap $ TKSubset k
  element                   = wrap TElt
  o (Wrap f) (Wrap g)       = wrap $ f :.:: g
  Wrap f >< Wrap g          = wrap $ f :><:: g
  Wrap f @@ Wrap g          = wrap $ f :@:: g
  ofSize (Wrap f) p         = wrap $ TOfSize f p
  ofSizeExactly (Wrap f) n  = wrap $ TOfSizeExactly f n
  nonEmpty (Wrap f)         = wrap $ TNonEmpty f
  rec f                     = wrap $ TRec f
  omega                     = wrap TOmega

------------------------------------------------------------
--  Reify/reflect  -----------------------------------------
------------------------------------------------------------

-- | Reify a species expression into an AST.  (Actually, this is just
--   the identity function with a usefully restricted type.)  For
--   example:
--
-- > > reify octopus
-- > C . TL+
-- > > reify (ksubset 3)
-- > E3 * TE
reify :: SpeciesAST -> SpeciesAST
reify = id

-- | The same as reify, but produce a typed, size-annotated AST.
reifyE :: ESpeciesAST -> ESpeciesAST
reifyE = id

-- | Reflect an AST back into any instance of the 'Species' class.
reflect :: Species s => SpeciesAST -> s
reflect Zero                = zero
reflect One                 = one
reflect (N n)               = fromInteger n
reflect X                   = singleton
reflect E                   = set
reflect C                   = cycle
reflect L                   = linOrd
reflect Subset              = subset
reflect (KSubset k)         = ksubset k
reflect Elt                 = element
reflect (f :+ g)            = reflect f + reflect g
reflect (f :* g)            = reflect f * reflect g
reflect (f :. g)            = reflect f `o` reflect g
reflect (f :>< g)           = reflect f >< reflect g
reflect (f :@ g)            = reflect f @@ reflect g
reflect (Der f)             = oneHole (reflect f)
reflect (OfSize f p)        = ofSize (reflect f) p
reflect (OfSizeExactly f n) = ofSizeExactly (reflect f) n
reflect (NonEmpty f)        = nonEmpty (reflect f)
reflect (Rec f)             = rec f
reflect Omega               = omega

-- | Reflect a typed AST back into any instance of the 'Species'
-- class.
reflectT :: Species s => TSpeciesAST f -> s
reflectT = reflect . erase'

-- | Reflect an existentially wrapped typed AST back into any
-- instance of the 'Species' class.
reflectE :: Species s => ESpeciesAST -> s
reflectE = reflect . erase
