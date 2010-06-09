{-# LANGUAGE NoImplicitPrelude, GADTs #-}

-- | Functions to manipulate and simplify species expressions
--   according to algebraic species isomorphisms.
module Math.Combinatorics.Species.Simplify
    ( simplify
    ) where

import NumericPrelude
import PreludeBase

import Math.Combinatorics.Species
import Math.Combinatorics.Species.AST

import Data.Typeable

simplify :: ESpeciesAST -> ESpeciesAST
simplify (Wrap (Sized _ f)) = simplify' f

simplify' :: SpeciesAST f -> ESpeciesAST
simplify' f@Zero        = wrap f
simplify' f@One         = wrap f
simplify' (N 0)         = wrap Zero
simplify' (N 1)         = wrap One
simplify' f@(N _)       = wrap f
simplify' f@X           = wrap f
simplify' f@E           = wrap f
simplify' f@C           = wrap f
simplify' f@L           = wrap f
simplify' f@Subset      = wrap f
simplify' f@(KSubset _) = wrap f
simplify' f@Elt         = wrap f
simplify' (f :+: g)     = simplSum (simplify' (stripI f)) (simplify' (stripI g))
simplify' (f :*: g)     = simplProd (simplify' (stripI f)) (simplify' (stripI g))

simplSum :: ESpeciesAST -> ESpeciesAST -> ESpeciesAST
simplSum (Wrap (Sized _ f)) (Wrap (Sized _ g)) = simplSum' f g

simplSum' :: (Typeable1 f, Typeable1 g) => SpeciesAST f -> SpeciesAST g -> ESpeciesAST
simplSum' Zero g = wrap g
simplSum' f Zero = wrap f
simplSum' One One = wrap (N 2)
simplSum' One (N n) = wrap (N (succ n))
simplSum' (N n) One = wrap (N (succ n))
simplSum' (N m) (N n) = wrap (N (m + n))

simplProd :: ESpeciesAST -> ESpeciesAST -> ESpeciesAST
simplProd (Wrap (Sized _ f)) (Wrap (Sized _ g)) = simplProd' f g

simplProd' :: (Typeable1 f, Typeable1 g) => SpeciesAST f -> SpeciesAST g -> ESpeciesAST
simplProd' Zero _ = wrap Zero
simplProd' _ Zero = wrap Zero
simplProd' One g  = wrap g
simplProd' f One  = wrap f
simplProd' (N m) (N n) = wrap (N (m * n))
simplProd' (f1 :+: f2) g = simplSum (simplProd' (stripI f1) g) (simplProd' (stripI f2) g)
