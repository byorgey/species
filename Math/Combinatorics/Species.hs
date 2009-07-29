{-# LANGUAGE NoImplicitPrelude #-}

-- | A DSL for describing and computing with combinatorial species.
--   This module re-exports the most generally useful functionality;
--   for more specialized functionality (for example, computing
--   directly with cycle index series), see the various sub-modules.
--
--   Note that this library makes extensive use of the numeric-prelude
--   library; to use it you will want to use -XNoImplicitPrelude, and
--   import NumericPrelude and PreludeBase.
--
--   For a friendly introduction to combinatorial species in general
--   and this library in particular, see my series of blog posts:
--
--     <http://byorgey.wordpress.com/2009/07/24/introducing-math-combinatorics-species/>
--
--   For a good reference (really, the
--   only English-language reference!) on combinatorial species, see
--   Bergeron, Labelle, and Leroux, \"Combinatorial Species and
--   Tree-Like Structures\", Vol. 67 of the Encyclopedia of
--   Mathematics and its Applications, Gian-Carlo Rota, ed., Cambridge
--   University Press, 1998.
module Math.Combinatorics.Species
    ( -- * The combinatorial species DSL
      -- $DSL
      Species(..)

      -- ** Convenience methods
      -- $synonyms

    , oneHole
    , madeOf
    , (><), (@@)
    , x, sets, cycles
    , subsets
    , ksubsets
    , elements

      -- ** Derived operations
    , pointed

      -- ** Derived species
    , list, lists
    , octopus, octopi
    , partition, partitions
    , permutation, permutations
    , ballot, ballots
    , simpleGraph, simpleGraphs
    , directedGraph, directedGraphs

      -- * Computing with species
    , labelled
    , unlabelled

      -- * Generating species structures
    , generate

    , generateTyped
    , structureType

      -- ** Types used for generation
      -- $types
    , Identity(..), Const(..)
    , Sum(..), Prod(..), Comp(..)
    , Star(..), Cycle(..), Set(..)

      -- * Species AST
      -- $ast
    , SpeciesTypedAST(..)
    , SpeciesAST(..)
    , reify
    , reflect

    ) where

import Math.Combinatorics.Species.Types
import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Labelled
import Math.Combinatorics.Species.Unlabelled
import Math.Combinatorics.Species.Generate
import Math.Combinatorics.Species.AST

-- $DSL
-- The combinatorial species DSL consists of the 'Species' type class,
-- which defines some primitive species and species operations.
-- Expressions of type @Species s => s@ can then be interpreted at
-- various instance types in order to compute with species in various
-- ways.

-- $synonyms
-- Some synonyms are provided for convenience.  In particular,
-- gramatically it can often be convenient to have both the singular
-- and plural versions of species, for example, @set \`o\` nonEmpty
-- sets@.

-- $types
-- Many of these functors are defined elsewhere; but to avoid a
-- plethora of imports, inconsistent naming/instance schemes, we just
-- redefine them here.

-- $ast
-- Species can be converted to and from 'SpeciesAST' via the functions
-- 'reify' and 'reflect'.