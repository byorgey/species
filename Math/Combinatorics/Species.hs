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
--   * <http://byorgey.wordpress.com/2009/07/24/introducing-math-combinatorics-species/>
--
--   * <http://byorgey.wordpress.com/2009/07/30/primitive-species-and-species-operations/>
--
--   * <http://byorgey.wordpress.com/2009/07/31/primitive-species-and-species-operations-part-ii/>
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

      -- Explicitly export methods of the Species class since
      -- we don't want to export all of them

      Species ( singleton, set, cycle, bracelet, linOrd
              , subset, ksubset, element
              , o, (><), (@@)
              , ofSize, ofSizeExactly, nonEmpty
              , rec
              )

      -- ** Convenience methods
      -- $synonyms

    , oneHole
    , x, sets, cycles, bracelets
    , linOrds
    , subsets
    , ksubsets
    , elements

      -- ** Derived operations
    , pointed

      -- ** Derived species
    , octopus, octopi
    , partition, partitions
    , permutation, permutations
    , ballot, ballots
    , simpleGraph, simpleGraphs
    , directedGraph, directedGraphs

      -- * Counting species structures
      -- $counting
    , labeled, labelled
    , unlabeled, unlabelled

      -- * Enumerating species structures
      -- $enum
    , Enumerable(..)
    , structureType
    , enumerate
    , enumerateL
    , enumerateU
    , enumerateM
    , enumerateAll, enumerateAllU

      -- ** Types used for generation
      -- $types
    , Void, Unit(..)
    , Id(..), Const(..)
    , (:+:)(..), (:*:)(..), (:.:)(..)
    , Star(..), Cycle(..), Set(..)

      -- * Species AST
      -- $ast
    , SpeciesAST
    , reify
    , reflect

    , TSpeciesAST
    , ESpeciesAST

    , wrap, unwrap
    , erase, erase', annotate

      -- * Species simplification

    , simplify
    , sumOfProducts

      -- * Recursive species
      -- $rec

    , ASTFunctor(..)
    , Interp
    , newtonRaphsonRec
    , newtonRaphson

      -- * Template Haskell
    , deriveDefaultSpecies
    , deriveSpecies

    ) where

import           Math.Combinatorics.Species.AST
import           Math.Combinatorics.Species.AST.Instances
import           Math.Combinatorics.Species.Class
import           Math.Combinatorics.Species.Enumerate
import           Math.Combinatorics.Species.Labeled
import           Math.Combinatorics.Species.NewtonRaphson
import           Math.Combinatorics.Species.Simplify
import           Math.Combinatorics.Species.Structures
import           Math.Combinatorics.Species.TH
import           Math.Combinatorics.Species.Unlabeled

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

-- $counting

-- $enum

-- $types
-- Many of these functors are already defined elsewhere, in other
-- packages; but to avoid a plethora of imports, inconsistent
-- naming/instance schemes, etc., we just redefine them here.

-- $ast
-- Species expressions can be reified into one of several AST types.

-- $rec
-- Tools for dealing with recursive species.
