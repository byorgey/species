{-# LANGUAGE NoImplicitPrelude #-}

module Math.Combinatorics.Species.Class where

import qualified Algebra.Differential as Differential

import NumericPrelude
import PreludeBase hiding (cycle)

--------------------------------------------------------------------------------
-- The class of species --------------------------------------------------------
--------------------------------------------------------------------------------

infixr 5 .:

-- Differential requires s to be a differentiable ring.
class (Differential.C s) => Species s where
  singleton :: s             -- the species X of singletons
  set       :: s             -- the species E of sets
  cycle     :: s             -- the species C of cyclical orderings (cycles)
  o         :: s -> s -> s   -- partitional composition
  nonEmpty  :: s -> s
  (.:)      :: s -> s -> s   -- XXX

-- Some convenient synonyms and derived operations.
pointed, oneHole :: (Species s) => s -> s  
pointed = (singleton *) . Differential.differentiate
oneHole = Differential.differentiate

madeOf :: Species s => s -> s -> s
madeOf = o

x, singletons, e, sets, cycles :: Species s => s
x          = singleton
singletons = singleton
e          = set
sets       = set
cycles     = cycle

-- Derived species.
list, lists :: Species s => s
list  = oneHole cycle
lists = list

octopus, octopi :: Species s => s
octopus = cycle `o` nonEmpty lists
octopi  = octopus

partition, partitions :: Species s => s
partition  = set `o` nonEmpty sets
partitions = partition

