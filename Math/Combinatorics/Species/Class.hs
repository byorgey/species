{-# LANGUAGE NoImplicitPrelude #-}

-- | The Species type class, which defines a small DSL for describing
--   combinatorial species.  Other modules in this library provide
--   specific instances which allow computing various properties of
--   combinatorial species.
module Math.Combinatorics.Species.Class
    (
      -- * The Species type class
      Species(..)

      -- * Convenience methods
      -- $synonyms

    , oneHole
    , madeOf
    , x
    , e
    , sets
    , cycles

      -- * Derived operations
      -- $derived_ops

    , pointed

      -- * Derived species
      -- $derived

    , list, lists
    , octopus, octopi
    , partition, partitions

    ) where

import qualified Algebra.Differential as Differential

import NumericPrelude
import PreludeBase hiding (cycle)

infixr 5 .:

-- | The Species type class.  Note that the @Differential@ constraint
--   requires s to be a differentiable ring, which means that every
--   instance must also implement instances for "Algebra.Additive"
--   (the species 0 and species addition, i.e. disjoint sum),
--   "Algebra.Ring" (the species 1 and species multiplication,
--   i.e. partitional product), and "Algebra.Differential" (species
--   differentiation, i.e. adjoining a distinguished element).
--
--   Note that the 'o' operation can be used infix to suggest common
--   notation for composition, and also to be read as an abbreviation
--   for \"of\", as in \"top o' the mornin'\": @set \`o\` nonEmpty
--   sets@.
class (Differential.C s) => Species s where

  -- | the species X of singletons
  singleton :: s

  -- | the species E of sets
  set       :: s

  -- | the species C of cyclical orderings (cycles/rings)
  cycle     :: s

  -- | partitional composition
  o         :: s -> s -> s

  -- | don't put a structure on the empty set
  nonEmpty  :: s -> s

  -- | @s1 .: s2@ is the species which puts an s1 structure on the
  --   empty set and an s2 structure on anything else.  Useful for
  --   getting recursively defined species off the ground.
  (.:)      :: s -> s -> s

-- $synonyms
-- Some synonyms are provided for convenience.  In particular,
-- gramatically it can often be convenient to have both the singular
-- and plural versions of species, for example, @set \`o\` nonEmpty
-- sets@.

-- | A convenient synonym for differentiation.  F'-structures look
--   like F-structures on a set formed by adjoining a distinguished
--   \"hole\" element to the underlying set.
oneHole :: (Species s) => s -> s
oneHole = Differential.differentiate

-- | A synonym for 'o' (partitional composition).
madeOf :: Species s => s -> s -> s
madeOf = o

-- | A synonym for 'singleton'.
x :: Species s => s
x          = singleton

-- | A synonym for 'set'.
e :: Species s => s
e          = set

sets :: Species s => s
sets       = set

cycles :: Species s => s
cycles     = cycle

-- $derived_ops
-- Some derived operations on species.

-- | Combinatorially, the operation of pointing picks out a
--   distinguished element from an underlying set.  It is equivalent
--   to the operator @x d/dx@.
pointed :: Species s => s -> s
pointed = (x *) . Differential.differentiate


-- $derived
-- Some species that can be defined in terms of the primitive species
-- operations.

-- | The species of linear orderings (lists).
list :: Species s => s
list  = oneHole cycle

-- | A convenient synonym for 'list'.
lists :: Species s => s
lists = list

-- | An octopus is a cyclic arrangement of lists, so called because
--   the lists look like \"tentacles\" attached to the cyclic
--   \"body\".
octopi, octopus :: Species s => s
octopus = cycle `o` nonEmpty lists
octopi  = octopus

-- | The species of set partitions is just the composition E o E+,
--   that is, sets of nonempty sets.
partitions, partition :: Species s => s
partition  = set `o` nonEmpty sets
partitions = partition

