{-# LANGUAGE NoImplicitPrelude #-}

-- | A DSL for describing combinatorial species and computing various
--   properties. This module re-exports the most generally useful
--   functionality; for more specialized functionality (for example,
--   computing directly with cycle index series), see the various
--   sub-modules.
--
--   Note that this library makes extensive use of the numeric-prelude
--   library; to use it you will want to use -XNoImplicitPrelude, and
--   import NumericPrelude and PreludeBase.
--
--   For a good reference (really, the only English-language
--   reference!) on combinatorial species, see Bergeron, Labelle, and
--   Leroux, \"Combinatorial Species and Tree-Like Structures\",
--   Vol. 67 of the Encyclopedia of Mathematics and its Applications,
--   Gian-Carlo Rota, ed., Cambridge University Press, 1998.
module Math.Combinatorics.Species
    ( -- * The combinatorial species DSL
      Species(..)

      -- ** Convenience methods
    , oneHole
    , madeOf
    , x, e, sets, cycles
          
      -- ** Derived operations
    , pointed
    , nonEmpty

      -- ** Derived species
    , list, lists
    , element, elements
    , octopus, octopi
    , partition, partitions
    , permutation, permutations
    , subset, subsets
    , ballot, ballots

      -- * Computing with species
    , labelled
    , unlabelled
    , generate

    ) where

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Labelled
import Math.Combinatorics.Species.Unlabelled
import Math.Combinatorics.Species.Generate
  

