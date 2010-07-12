{-# LANGUAGE NoImplicitPrelude #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Math.Combinatorics.Species.Class
-- Copyright   :  (c) Brent Yorgey 2010
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@cis.upenn.edu
-- Stability   :  experimental
--
-- The Species type class, which defines a small DSL for describing
-- combinatorial species.  Other modules in this library provide
-- specific instances which allow computing various properties of
-- combinatorial species.
--
-----------------------------------------------------------------------------

module Math.Combinatorics.Species.Class
    (
      -- * The Species type class
      Species(..)

      -- * Convenience methods

    , oneHole
    , x

      -- ** Plurals

      -- | It can be grammatically convenient to define plural
      -- versions of species as synonyms for the singular versions.
      -- For example, we can use @'set' ``o`` 'nonEmpty' 'sets'@
      -- instead of @'set' ``o`` 'nonEmpty' 'set'@.
    , sets
    , cycles
    , linOrds
    , subsets
    , ksubsets
    , elements

      -- * Derived operations
      -- $derived_ops

    , pointed

      -- * Derived species
      -- $derived

    , octopus, octopi
    , partition, partitions
    , permutation, permutations
    , ballot, ballots
    , simpleGraph, simpleGraphs
    , directedGraph, directedGraphs

    ) where

import qualified Algebra.Differential as Differential

import NumericPrelude
import PreludeBase hiding (cycle)

import Math.Combinatorics.Species.AST

-- | The Species type class.  Note that the @Differential@ constraint
--   requires s to be a differentiable ring, which means that every
--   instance must also implement instances for "Algebra.Additive"
--   (the species 0 and species addition, i.e. disjoint sum),
--   "Algebra.Ring" (the species 1 and species multiplication,
--   i.e. partitional product), and "Algebra.Differential" (species
--   differentiation, i.e. adjoining a distinguished element).
--
--   Minimal complete definition: 'singleton', 'set', 'cycle', 'o',
--   'cartesian', 'fcomp', 'ofSize'.
--
--   Note that the 'o' operation can be used infix to suggest common
--   notation for composition, and also to be read as an abbreviation
--   for \"of\", as in \"top o' the mornin'\": @set \`o\` nonEmpty
--   sets@.
class (Differential.C s) => Species s where

  -- | The species @X@ of singletons. Puts a singleton structure on an
  --   underlying label set of size 1, and no structures on any other
  --   underlying label sets.  'x' is also provided as a synonym.
  singleton :: s

  -- | The species @E@ of sets.  Puts a singleton structure on /any/
  --   underlying label set.
  set :: s

  -- | The species @C@ of cyclical orderings (cycles/rings).
  cycle :: s

  -- | The species @L@ of linear orderings (lists). Since linear
  --   orderings are isomorphic to cyclic orderings with a hole, we
  --   may take @'linOrd' = 'oneHole' 'cycle'@ as the default
  --   implementation; 'linOrd' is included in the 'Species' class so it
  --   can be special-cased for enumeration.
  linOrd :: s
  linOrd = oneHole cycle

  -- | The species @p@ of subsets is given by @'subset' = 'set' *
  --   'set'@. 'subset' is included in the 'Species' class so it can
  --   be overridden when enumerating structures: by default the
  --   enumeration code would generate a pair of the subset and its
  --   complement, but normally when thinking about subsets we only
  --   want to see the elements in the subset.  To explicitly
  --   enumerate subset/complement pairs, you can use @'set' * 'set'@
  --   directly.
  subset :: s
  subset = set * set

  -- | Subsets of size exactly k, @'ksubset' k = ('set'
  -- ``ofSizeExactly`` k) * 'set'@.  Included with a default definition
  -- in the 'Species' class for the same reason as 'subset'.
  ksubset :: Integer -> s
  ksubset k = (set `ofSizeExactly` k) * set

  -- | Structures of the species @e@ of elements are just elements of
  --   the underlying set, @'element' = 'singleton' * 'set'@.  Included
  --   with a default definition in 'Species' class for the same
  --   reason as 'subset' and 'ksubset'.
  element :: s
  element = singleton * set

  -- | Partitional composition.  To form all @(f ``o`` g)@-structures on
  --   the underlying label set U, first form all set partitions of U;
  --   for each partition @p@, put an @f@-structure on the classes of
  --   @p@, and a separate @g@-structure on the elements in each
  --   class.
  o :: s -> s -> s

  -- | Cartisian product of two species.  An @(f '><' g)@-structure
  -- consists of an @f@-structure superimposed on a @g@-structure over
  -- the same underlying set.
  (><) :: s -> s -> s

  -- | Functor composition of two species.  An @(f '@@' g)@-structure
  --   consists of an @f@-structure on the set of all @g@-structures.
  (@@) :: s -> s -> s

  -- | Only put a structure on underlying sets whose size satisfies
  --   the predicate.
  ofSize :: s -> (Integer -> Bool) -> s

  -- | Only put a structure on underlying sets of the given size.  A
  --   default implementation of @ofSize (==k)@ is provided, but this
  --   method is included in the 'Species' class as a special case
  --   since it can be more efficient: we get to turn infinite lists
  --   of coefficients into finite ones.
  ofSizeExactly :: s -> Integer -> s
  ofSizeExactly s n = s `ofSize` (==n)

  -- | Don't put a structure on the empty set.  The default definition
  --   uses 'ofSize'; included in the 'Species' class so it can be
  --   overriden in special cases (such as when reifying species
  --   expressions).
  nonEmpty :: s -> s
  nonEmpty = flip ofSize (>0)

  -- | 'rec f' is the least fixpoint of (the interpretation of) the
  --   higher-order species constructor 'f'.
  rec :: ASTFunctor f => f -> s

  -- | Omega is the pseudo-species which only puts a structure on
  --   infinite label sets.  Of course this is not really a species,
  --   but it is sometimes a convenient fiction to use Omega to stand
  --   in for recursive occurrences of a species.
  omega :: s

-- | A convenient synonym for differentiation.  @'oneHole'
-- f@-structures look like @f@-structures on a set formed by adjoining
-- a distinguished \"hole\" element to the underlying set.
oneHole :: (Species s) => s -> s
oneHole = Differential.differentiate

-- | A synonym for 'singleton'.
x :: Species s => s
x = singleton

sets :: Species s => s
sets = set

cycles :: Species s => s
cycles = cycle

-- $derived_ops
-- Some derived operations on species.

-- | Intuitively, the operation of pointing picks out a
--   distinguished element from an underlying set.  It is equivalent
--   to the operator @x d/dx@: @'pointed' s = 'singleton' * 'differentiate' s@.
pointed :: Species s => s -> s
pointed = (x *) . Differential.differentiate

-- $derived
-- Some species that can be defined in terms of the primitive species
-- operations.

linOrds :: Species s => s
linOrds = linOrd

elements :: Species s => s
elements = element

-- | An octopus is a cyclic arrangement of lists, so called because
--   the lists look like \"tentacles\" attached to the cyclic
--   \"body\": @'octopus' = 'cycle' ``o`` 'nonEmpty' 'linOrds'@.
octopi, octopus :: Species s => s
octopus = cycle `o` nonEmpty linOrds
octopi  = octopus

-- | The species of set partitions is just the composition @'set'
-- ``o`` 'nonEmpty' 'sets'@.
partitions, partition :: Species s => s
partition  = set `o` nonEmpty sets
partitions = partition

-- | A permutation is a set of disjoint cycles: @'permutation' = 'set'
-- ``o`` 'cycles'@.
permutations, permutation :: Species s => s
permutation = set `o` cycles
permutations = permutation

subsets :: Species s => s
subsets = subset

-- | The species of ballots consists of linear orderings of
--   nonempty sets: @'ballot' = 'linOrd' ``o`` 'nonEmpty' 'sets'@.
ballots, ballot :: Species s => s
ballot = linOrd `o` nonEmpty sets
ballots = ballot

ksubsets :: Species s => Integer -> s
ksubsets = ksubset

-- | Simple graphs (undirected, without loops). A simple graph is a
--   subset of the set of all size-two subsets of the vertices:
--   @'simpleGraph' = 'subset' '@@' ('ksubset' 2)@.
simpleGraphs, simpleGraph :: Species s => s
simpleGraph = subset @@ (ksubset 2)
simpleGraphs = simpleGraph

-- | A directed graph (with loops) is a subset of all pairs drawn
--   (with replacement) from the set of vertices: @'subset' '@@'
--   ('element' '><' 'element')@.  It can also be thought of as the
--   species of binary relations.
directedGraphs, directedGraph :: Species s => s
directedGraph = subset @@ (element >< element)
directedGraphs = directedGraph