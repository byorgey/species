{-# LANGUAGE NoImplicitPrelude
           , GADTs
           , EmptyDataDecls
  #-}
module Math.Combinatorics.Species.Algebra where

import Math.Combinatorics.Species.Class

import qualified Algebra.Additive as Additive
import qualified Algebra.Ring as Ring
import qualified Algebra.Differential as Differential

import NumericPrelude
import PreludeBase hiding (cycle)

class Functor f => ShowF f where
  showF :: (Show a) => f a -> String

-- instance (ShowF f, Show a) => Show (f a) where
--   show = showF

data Z
data S n
data X
data (:+:) f g
data (:*:) f g
data (:.:) f g
data Der f
data E
data C
data NonEmpty f

data SpeciesAlgT s where
   O        :: SpeciesAlgT Z
   I        :: SpeciesAlgT (S Z)
   X        :: SpeciesAlgT X
   (:+:)    :: (ShowF (StructureF f), ShowF (StructureF g)) 
            => SpeciesAlgT f -> SpeciesAlgT g -> SpeciesAlgT (f :+: g)
   (:*:)    :: (ShowF (StructureF f), ShowF (StructureF g))
            => SpeciesAlgT f -> SpeciesAlgT g -> SpeciesAlgT (f :*: g)
   (:.:)    :: (ShowF (StructureF f), ShowF (StructureF g)) 
            => SpeciesAlgT f -> SpeciesAlgT g -> SpeciesAlgT (f :.: g)
   Der      :: (ShowF (StructureF f)) 
            => SpeciesAlgT f -> SpeciesAlgT (Der f)
   E        :: SpeciesAlgT E
   C        :: SpeciesAlgT C
   NonEmpty :: (ShowF (StructureF f)) 
            => SpeciesAlgT f -> SpeciesAlgT (NonEmpty f)

hasCompT :: SpeciesAlgT s -> Bool
hasCompT (f :+: g) = hasCompT f || hasCompT g
hasCompT (f :*: g) = hasCompT f || hasCompT g
hasCompT (_ :.: _) = True
hasCompT (NonEmpty f) = hasCompT f
hasCompT _ = False

hasDerT :: SpeciesAlgT s -> Bool
hasDerT (f :+: g) = hasDerT f || hasDerT g
hasDerT (f :*: g) = hasDerT f || hasDerT g
hasDerT (f :.: g) = hasDerT f || hasDerT g
hasDerT (Der _) = True
hasDerT (NonEmpty f) = hasDerT f
hasDerT _ = False

-- existential wrapper
data SpeciesAlg where
  SA :: (ShowF (StructureF s)) => SpeciesAlgT s -> SpeciesAlg

hasComp :: SpeciesAlg -> Bool
hasComp (SA s) = hasCompT s

hasDer :: SpeciesAlg -> Bool
hasDer (SA s) = hasDerT s

instance Additive.C SpeciesAlg where
  zero   = SA O
  (SA f) + (SA g) = SA (f :+: g)
  negate = error "negation is not implemented yet!  wait until virtual species..."

instance Ring.C SpeciesAlg where
  (SA f) * (SA g) = SA (f :*: g)
  one = SA I

instance Differential.C SpeciesAlg where
  differentiate (SA f) = SA (Der f)

instance Species SpeciesAlg where
  singleton = SA X
  set       = SA E
  cycle     = SA C
  o (SA f) (SA g) = SA (f :.: g)
  nonEmpty (SA f) = SA (NonEmpty f)

reify :: SpeciesAlg -> SpeciesAlg
reify = id

reflectT :: Species s => SpeciesAlgT f -> s
reflectT O = zero
reflectT I = one
reflectT X = singleton
reflectT (f :+: g) = reflectT f + reflectT g
reflectT (f :*: g) = reflectT f * reflectT g
reflectT (f :.: g) = reflectT f `o` reflectT g
reflectT (Der f)   = oneHole (reflectT f)
reflectT E = set
reflectT C = cycle
reflectT (NonEmpty f) = nonEmpty (reflectT f)

reflect :: Species s => SpeciesAlg -> s
reflect (SA f) = reflectT f

-- -- This is the basic idea: to do this right, we really want a more
-- --   sophisticated rewriting system.
-- simplify :: SpeciesAlg -> SpeciesAlg
-- simplify (N n :+: N m) = N (n+m)
-- simplify (N n :*: N m) = N (n*m)
-- simplify (N 0 :+: s)   = simplify s
-- simplify (s :+: N 0)   = simplify s
-- simplify (N 0 :*: s)   = N 0
-- simplify (s :*: N 0)   = N 0
-- simplify (f :+: g)     = simplify $ simplify f :+: simplify g
-- simplify (f :*: g)     = simplify f :*: simplify g
-- simplify (f :.: g)     = simplify f :.: simplify g
-- simplify (Der f)       = Der $ simplify f
-- simplify s = s
