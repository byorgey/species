{-# LANGUAGE GADTs #-}

-- | Type class instances for 'ESpeciesAST' and 'SpeciesAST', in a
--   separate module to avoid a dependency cycle between
--   "Math.Combinatorics.Species.AST" and
--   "Math.Combinatorics.Species.Class".
module Math.Combinatorics.Species.AST.Instances
    ( reify, reflectT, reflect )
    where

import NumericPrelude
import PreludeBase hiding (cycle)

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.AST

import qualified Algebra.Additive as Additive
import qualified Algebra.Ring as Ring
import qualified Algebra.Differential as Differential

instance Show (SpeciesAST s) where
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
  showsPrec p (f :+: g)           = showParen (p>6)  $ showsPrec 6 f . showString " + "  . showsPrec 6 g
  showsPrec p (f :*: g)           = showParen (p>=7) $ showsPrec 7 f . showString " * "  . showsPrec 7 g
  showsPrec p (f :.: g)           = showParen (p>=7) $ showsPrec 7 f . showString " . "  . showsPrec 7 g
  showsPrec p (f :><: g)          = showParen (p>=7) $ showsPrec 7 f . showString " >< " . showsPrec 7 g
  showsPrec p (f :@: g)           = showParen (p>=7) $ showsPrec 7 f . showString " @ "  . showsPrec 7 g
  showsPrec p (Der f)             = showsPrec 11 f . showChar '\''
  showsPrec _ (OfSize f p)        = showChar '<' .  showsPrec 0 f . showChar '>'
  showsPrec _ (OfSizeExactly f n) = showsPrec 11 f . shows n
  showsPrec _ (NonEmpty f)        = showsPrec 11 f . showChar '+'
  showsPrec _ (Rec f)             = shows f

instance Show ESpeciesAST where
  show (Wrap f) = show f

instance Additive.C ESpeciesAST where
  zero   = Wrap Zero
  (Wrap f) + (Wrap g) = Wrap (f :+: g)
  negate = error "negation is not implemented yet!  wait until virtual species..."

instance Ring.C ESpeciesAST where
  (Wrap f) * (Wrap g) = Wrap (f :*: g)
  one = Wrap One
  fromInteger 0 = Wrap Zero
  fromInteger 1 = Wrap One
  fromInteger n = Wrap (N n)
  _ ^ 0 = one
  (Wrap f) ^ 1 = Wrap f
  (Wrap f) ^ n = case (Wrap f) ^ (n-1) of
                 (Wrap f') -> Wrap (f :*: f')

instance Differential.C ESpeciesAST where
  differentiate (Wrap f) = Wrap (Der f)

instance Species ESpeciesAST where
  singleton               = Wrap X
  set                     = Wrap E
  cycle                   = Wrap C
  linOrd                  = Wrap L
  subset                  = Wrap Subset
  ksubset k               = Wrap (KSubset k)
  element                 = Wrap Elt
  o (Wrap f) (Wrap g)         = Wrap (f :.: g)
  cartesian (Wrap f) (Wrap g) = Wrap (f :><: g)
  fcomp (Wrap f) (Wrap g)     = Wrap (f :@: g)
  ofSize (Wrap f) p         = Wrap (OfSize f p)
  ofSizeExactly (Wrap f) n  = Wrap (OfSizeExactly f n)
  nonEmpty (Wrap f)         = Wrap (NonEmpty f)
  rec f                   = Wrap (Rec f)

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
reflectT :: Species s => SpeciesAST f -> s
reflectT Zero                = 0
reflectT One                 = 1
reflectT (N n)               = fromInteger n
reflectT X                   = singleton
reflectT E                   = set
reflectT C                   = cycle
reflectT L                   = linOrd
reflectT Subset              = subset
reflectT (KSubset k)         = ksubset k
reflectT Elt                 = element
reflectT (f :+: g)           = reflectT f + reflectT g
reflectT (f :*: g)           = reflectT f * reflectT g
reflectT (f :.: g)           = reflectT f `o` reflectT g
reflectT (f :><: g)          = reflectT f >< reflectT g
reflectT (f :@: g)           = reflectT f @@ reflectT g
reflectT (Der f)             = oneHole (reflectT f)
reflectT (OfSize f p)        = ofSize (reflectT f) p
reflectT (OfSizeExactly f n) = ofSizeExactly (reflectT f) n
reflectT (NonEmpty f)        = nonEmpty (reflectT f)
reflectT (Rec f)             = rec f

-- | Reflect an AST back into any instance of the 'Species' class.
reflect :: Species s => ESpeciesAST -> s
reflect (Wrap f) = reflectT f
