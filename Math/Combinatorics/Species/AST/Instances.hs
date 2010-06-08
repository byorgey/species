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
import Math.Combinatorics.Species.Util.Interval hiding (omega)
import qualified Math.Combinatorics.Species.Util.Interval as I

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
  showsPrec p (f :+: g)           = showParen (p>6)  $ showsPrec 6 (stripI f)
                                                     . showString " + "
                                                     . showsPrec 6 (stripI g)
  showsPrec p (f :*: g)           = showParen (p>=7) $ showsPrec 7 (stripI f)
                                                     . showString " * "
                                                     . showsPrec 7 (stripI g)
  showsPrec p (f :.: g)           = showParen (p>=7) $ showsPrec 7 (stripI f)
                                                     . showString " . "
                                                     . showsPrec 7 (stripI g)
  showsPrec p (f :><: g)          = showParen (p>=7) $ showsPrec 7 (stripI f)
                                                     . showString " >< "
                                                     . showsPrec 7 (stripI g)
  showsPrec p (f :@: g)           = showParen (p>=7) $ showsPrec 7 (stripI f)
                                                     . showString " @ "
                                                     . showsPrec 7 (stripI g)
  showsPrec p (Der f)             = showsPrec 11 (stripI f) . showChar '\''
  showsPrec _ (OfSize f p)        = showChar '<' .  showsPrec 0 (stripI f) . showChar '>'
  showsPrec _ (OfSizeExactly f n) = showsPrec 11 (stripI f) . shows n
  showsPrec _ (NonEmpty f)        = showsPrec 11 (stripI f) . showChar '+'
  showsPrec _ (Rec f)             = shows f

instance Show ESpeciesAST where
  show (Wrap f) = show (stripI f)

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
reflectT (f :+: g)           = reflectT (stripI f) + reflectT (stripI g)
reflectT (f :*: g)           = reflectT (stripI f) * reflectT (stripI g)
reflectT (f :.: g)           = reflectT (stripI f) `o` reflectT (stripI g)
reflectT (f :><: g)          = reflectT (stripI f) >< reflectT (stripI g)
reflectT (f :@: g)           = reflectT (stripI f) @@ reflectT (stripI g)
reflectT (Der f)             = oneHole (reflectT $ stripI f)
reflectT (OfSize f p)        = ofSize (reflectT $ stripI f) p
reflectT (OfSizeExactly f n) = ofSizeExactly (reflectT $ stripI f) n
reflectT (NonEmpty f)        = nonEmpty (reflectT $ stripI f)
reflectT (Rec f)             = rec f
reflectT Omega               = omega

-- | Reflect an AST back into any instance of the 'Species' class.
reflect :: Species s => ESpeciesAST -> s
reflect (Wrap f) = reflectT (stripI f)
