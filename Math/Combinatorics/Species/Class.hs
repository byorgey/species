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
    , (><)
    , x
    , e
    , sets
    , cycles

      -- * Derived operations
      -- $derived_ops

    , pointed
    , nonEmpty

      -- * Derived species
      -- $derived

    , list, lists
    , element, elements
    , octopus, octopi
    , partition, partitions
    , permutation, permutations
    , subset, subsets
    , ballot, ballots
    , ksubset, ksubsets

    ) where

import qualified Algebra.Differential as Differential

import NumericPrelude
import PreludeBase hiding (cycle)

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

  -- | The species X of singletons
  singleton :: s

  -- | The species E of sets
  set       :: s

  -- | The species C of cyclical orderings (cycles/rings)
  cycle     :: s

  -- | Partitional composition
  o         :: s -> s -> s

  -- | Only put a structure on underlying sets whose size satisfies
  --   the predicate.
  ofSize    :: s -> (Integer -> Bool) -> s

  -- | Only put a structure on underlying sets of the given size.  We
  --   include this as a special case, instead of just using @ofSize
  --   (==k)@, since it can be more efficient: we get to turn infinite
  --   lists of coefficients into finite ones.
  ofSizeExactly :: s -> Integer -> s

  -- | Cartisian product of two species.  an F x G structure consists
  --   of an F structure superimposed on a G structure over the same
  --   labels.
  cartesian :: s -> s -> s


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

-- | A synonym for cartesian product.
(><) :: Species s => s -> s -> s
(><) = cartesian

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

-- | Don't put a structure on the empty set.
nonEmpty  :: Species s => s -> s
nonEmpty = flip ofSize (>0)


-- $derived
-- Some species that can be defined in terms of the primitive species
-- operations.

-- | The species L of linear orderings (lists): since lists are
--   isomorphic to cycles with a hole, we may take L = C'.
list :: Species s => s
list  = oneHole cycle

-- | A convenient synonym for 'list'.
lists :: Species s => s
lists = list

-- | Structures of the species eps of elements are just elements of
--   the underlying set: eps = X * E.
elements, element :: Species s => s
element = x * e
elements = element

-- | An octopus is a cyclic arrangement of lists, so called because
--   the lists look like \"tentacles\" attached to the cyclic
--   \"body\": Oct = C o E+ .
octopi, octopus :: Species s => s
octopus = cycle `o` nonEmpty lists
octopi  = octopus

-- | The species of set partitions is just the composition E o E+,
--   that is, sets of nonempty sets.
partitions, partition :: Species s => s
partition  = set `o` nonEmpty sets
partitions = partition

-- | A permutation is a set of disjoint cycles: S = E o C.
permutations, permutation :: Species s => s
permutation = set `o` cycles
permutations = permutation

-- | The species p of subsets is given by p = E * E.
subsets, subset :: Species s => s
subset = set * set
subsets = subset

-- | The species Bal of ballots consists of linear orderings of
--   nonempty sets: Bal = L o E+.
ballots, ballot :: Species s => s
ballot = list `o` nonEmpty sets
ballots = ballot

-- | Subsets of size exactly k, p[k] = E_k * E.
ksubsets, ksubset :: Species s => Integer -> s
ksubset k = (set `ofSizeExactly` k) * set
ksubsets = ksubset