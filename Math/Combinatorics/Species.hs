{-# LANGUAGE ExistentialQuantification
           , FlexibleInstances
           , FlexibleContexts
           , TypeOperators
           , GADTs
           , ScopedTypeVariables
           , EmptyDataDecls 
           , NoImplicitPrelude
  #-}

module CombSpecies where

import MyPrelude
import qualified MathObj.PowerSeries as PowerSeries
import qualified MathObj.EGF as EGF

import qualified Algebra.Additive as Additive
import qualified Algebra.Ring as Ring
import qualified Algebra.Differential as Differential

unimplemented :: String -> a
unimplemented = error . (++ " is not yet implemented.")

--------------------------------------------------------------------------------
-- The class of species --------------------------------------------------------
--------------------------------------------------------------------------------

-- Differential requires s to be a differentiable ring.
class (Differential.C s) => Species s where
  singleton :: s             -- the species X of singletons
  set       :: s             -- the species E of sets
  list      :: s             -- the species L of linear orderings
  o         :: s -> s -> s   -- partitional composition

-- Some convenient synonyms.
x, singletons, e, sets, lists :: Species s => s
x          = singleton
singletons = singleton
e          = set
sets       = set
lists      = list

pointed, oneHole :: (Species s) => s -> s  
pointed = (singleton *) . Differential.differentiate
oneHole = Differential.differentiate

madeOf :: Species s => s -> s -> s
madeOf = o

--------------------------------------------------------------------------------
-- Unlabelled enumeration (classical power series) -----------------------------
--------------------------------------------------------------------------------

instance Species (PowerSeries.T Integer) where
  singleton = PowerSeries.fromCoeffs [0,1]
  sets      = PowerSeries.fromCoeffs (repeat 1)
  lists     = PowerSeries.fromCoeffs (repeat 1)
  o         = unimplemented "unlabelled composition"

--------------------------------------------------------------------------------
-- Species algebra -------------------------------------------------------------
--------------------------------------------------------------------------------

data SpeciesAlg where
   N        :: Integer -> SpeciesAlg
   X        :: SpeciesAlg
   (:+:)    :: SpeciesAlg -> SpeciesAlg -> SpeciesAlg
   (:*:)    :: SpeciesAlg -> SpeciesAlg -> SpeciesAlg
   (:.:)    :: SpeciesAlg -> SpeciesAlg -> SpeciesAlg
   Der      :: SpeciesAlg -> SpeciesAlg
   E        :: SpeciesAlg
   L        :: SpeciesAlg
     deriving (Show)

instance Additive.C SpeciesAlg where
  zero   = N 0
  (+)    = (:+:)
  negate = error "negation is not implemented yet!  wait until virtual species..."

instance Ring.C SpeciesAlg where
  (*) = (:*:)
  one = N 1

instance Differential.C SpeciesAlg where
  differentiate = Der

instance Species SpeciesAlg where
  singleton = X
  sets      = E
  lists     = L
  o         = (:.:)

reflect :: Species s => SpeciesAlg -> s
reflect = undefined -- XXX

-- This is the basic idea: to do this right, we really want a more
--   sophisticated rewriting system.
simplify :: SpeciesAlg -> SpeciesAlg
simplify (N n :+: N m) = N (n+m)
simplify (N n :*: N m) = N (n*m)
simplify (N 0 :+: s)   = simplify s
simplify (s :+: N 0)   = simplify s
simplify (N 0 :*: s)   = N 0
simplify (s :*: N 0)   = N 0
simplify (f :+: g)     = simplify $ simplify f :+: simplify g
simplify (f :*: g)     = simplify f :*: simplify g
simplify (f :.: g)     = simplify f :.: simplify g
simplify (Der f)       = Der $ simplify f
simplify s = s

--------------------------------------------------------------------------------
-- Labelled enumeration (egf's) ------------------------------------------------
--------------------------------------------------------------------------------

facts :: [Integer]
facts = 1 : zipWith (*) [1..] facts

-- using this math library isn't really working out all that well.
--   need to think carefully about what I need and how to design it right.

-- two libraries, or one library with two types: one for egf's and one
--   for normal power series.  Importantly it should support
--   *division* on power series with *integral* coefficients: just
--   trust that this will always be true!  or maybe do some checks.

instance Species (EGF.T Integer) where
  singleton = EGF.fromCoeffs [0,1]
  sets      = EGF.fromCoeffs $ repeat 1
  lists     = EGF.fromCoeffs facts
  o         = unimplemented "labelled composition"

--------------------------------------------------------------------------------
-- Generation of species -------------------------------------------------------
--------------------------------------------------------------------------------

-- newtype (f :+@ g) a = Sum  { unSum  :: Either (f a) (g a) }
--   deriving (Show)
-- newtype (f :*@ g) a = Prod { unProd :: (f a, g a) }
--   deriving (Show)
-- newtype (f :.@ g) a = Comp { unComp :: (f (g a)) }
--   deriving (Show)

-- data O
-- data I
-- data E
-- data X
-- data L
-- data (:+:) a b
-- data (:*:) a b
-- data (:.:) a b
-- data Der a
-- data (:@:) a b


-- splits :: [a] -> [([a],[a])]
-- splits []     = [([],[])]
-- splits (x:xs) = map (first (x:)) ss ++ map (second (x:)) ss
--   where ss = splits xs

-- -- power set
-- pSet :: [a] -> [([a],[a])]
-- pSet [] = [([],[])]
-- pSet (x:xs) = mapx first ++ mapx second 
--   where mapx which = map (which (x:)) $ pSet xs

-- partitions :: [a] -> [[[a]]]
-- partitions [] = [[]]
-- partitions (s:s') = do (sub,compl) <- pSet s'
--                        let firstSubset = s:sub
--                        map (firstSubset:) $ partitions compl

-- permutations :: [a] -> [[a]]
-- permutations [] = [[]]
-- permutations (x:xs) = undefined  -- XXX

-- over :: forall a f. Species f -> [a] -> [f a]
-- over O _   = []
-- over I []  = [[]]
-- over I _   = []
-- over E ls  = [ls]
-- over X [l] = [[l]]
-- over X _   = []
-- over L ls  = permutations ls
-- over (f :+: g) ls = map (Sum . Left) (f `over` ls) ++ map (Sum . Right) (g `over` ls) 
-- over (f :*: g) ls = [ Prod (x, y) | (s1,s2) <- splits ls
--                                   ,       x <- f `over` s1
--                                   ,       y <- g `over` s2 
--                     ]
-- over (f :.: g) ls = [ Comp y | p  <- partitions ls
--                              , xs <- mapM (g `over`) p
--                              , y  <- f `over` xs 
--                     ]
-- over (Der f) ls   = f `over` (undefined : ls)
-- over (f :@: g) ls = map Comp $ f `over` (g `over` ls)
-- over (NonEmpty f) [] = []
-- over (NonEmpty f) ls = f `over` ls
