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
import Math.Combinatorics.Species.Util.Interval as I
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
  show (Wrap _ f) = show f

instance Additive.C ESpeciesAST where
  zero   = Wrap 0 Zero
  (Wrap fi f) + (Wrap gi g) = Wrap (fi `I.union` gi) (f :+: g)
  negate = error "negation is not implemented yet!  wait until virtual species..."

instance Ring.C ESpeciesAST where
  (Wrap fi f) * (Wrap gi g) = Wrap (fi + gi) (f :*: g)
  one = Wrap 0 One
  fromInteger 0 = Wrap 0 Zero
  fromInteger 1 = Wrap 0 One
  fromInteger n = Wrap 0 (N n)
  _ ^ 0 = one
  w@(Wrap{}) ^ 1 = w
  (Wrap fi f) ^ n   = case (Wrap fi f) ^ (n-1) of
                        (Wrap f'i f') -> Wrap (fi + f'i) (f :*: f')

instance Differential.C ESpeciesAST where
  differentiate (Wrap fi f) = Wrap (decrI fi) (Der f)

instance Species ESpeciesAST where
  singleton                         = Wrap 1             X
  set                               = Wrap allNats       E
  cycle                             = Wrap (allNats + 1) C
  linOrd                            = Wrap allNats       L
  subset                            = Wrap allNats       Subset
  ksubset k                         = Wrap (allNats + fromInteger k) (KSubset k)
  element                           = Wrap (allNats + 1) Elt
  o (Wrap fi f) (Wrap gi g)         = Wrap (fi * gi)     (f :.: g)
  cartesian (Wrap fi f) (Wrap gi g) = Wrap (fi `I.intersect` gi) (f :><: g)
  fcomp (Wrap fi f) (Wrap gi g)     = Wrap allNats       (f :@: g)
    -- Note, the above is obviously overly conservative.  To do this
    -- right we'd have to compute the generating function for g ---
    -- and actually it would depend on whether we were doing labelled
    -- or unlabelled enumeration, which we don't know at this point.
  ofSize (Wrap fi f) p              = Wrap (I (smallestIn fi p) Omega) (OfSize f p)
  ofSizeExactly (Wrap fi f) n       = Wrap (fromInteger n) (OfSizeExactly f n)
  nonEmpty (Wrap fi f)              = Wrap (fi `I.intersect` (I 1 Omega)) (NonEmpty f)
  rec f                             = Wrap undefined (Rec f)
    -- XXX fix this!  Somehow need to "solve" the recursive interval equation
    -- that we get.

smallestIn :: Interval -> (Integer -> Bool) -> Integer
smallestIn (I s _) p = head $ filter p [s..]

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
reflect (Wrap _ f) = reflectT f
