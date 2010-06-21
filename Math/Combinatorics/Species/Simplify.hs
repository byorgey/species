{-# LANGUAGE NoImplicitPrelude, GADTs #-}

-- | Functions to manipulate and simplify species expressions
--   according to algebraic species isomorphisms.
module Math.Combinatorics.Species.Simplify
    ( simplify, sumOfProducts
    ) where

import NumericPrelude
import PreludeBase

import Math.Combinatorics.Species.AST
import Math.Combinatorics.Species.AST.Instances

import Data.List (genericLength)
import Data.Typeable

simplify :: SpeciesAST -> SpeciesAST
simplify Zero          = Zero
simplify One           = One
simplify (N 0)         = Zero
simplify (N 1)         = One
simplify f@(N _)       = f
simplify X             =  X
simplify E             =  E
simplify C             =  C
simplify L             =  L
simplify Subset        =  Subset
simplify f@(KSubset _) =  f
simplify Elt           =  Elt
simplify (f :+: g)     = simplSum (simplify f) (simplify g)
simplify (f :*: g)     = simplProd (simplify f) (simplify g)
simplify (f :.: g)     = simplComp (simplify f) (simplify g)
simplify (f :><: g)    = simplCart (simplify f) (simplify g)
simplify (f :@: g)     = simplFunc (simplify f) (simplify g)
simplify (Der f)       = simplDer (simplify f)
simplify (OfSize f p)  = simplOfSize (simplify f) p
simplify (OfSizeExactly f k) = simplOfSizeExactly (simplify f) k
simplify (NonEmpty f)  = simplNonEmpty (simplify f)
simplify (Rec f)       = Rec f
simplify Omega         = Omega

simplSum :: SpeciesAST -> SpeciesAST -> SpeciesAST
simplSum Zero g                               = g
simplSum f Zero                               = f
simplSum One One                             = N 2
simplSum One (N n)                           = N $ succ n
simplSum (N n) One                           = N $ succ n
simplSum (N m) (N n)                         = N $ m + n
simplSum One (One :+: g)                    = simplSum (N 2) g
simplSum One ((N n) :+: g)                  = simplSum (N $ succ n) g
simplSum (N n) (One :+: g)                  = simplSum (N $ succ n) g
simplSum (N m) ((N n) :+: g)                = simplSum (N (m + n)) g
simplSum (f :+: g) h                          = simplSum f (simplSum g h)
simplSum f g | f == g                          = simplProd (N 2) f
simplSum f (g :+: h) | f == g                 = simplSum (simplProd (N 2) f) h
simplSum (N n :*: f) g | f == g              = N (succ n) :*: f
simplSum f (N n :*: g) | f == g              = N (succ n) :*: f
simplSum (N m :*: f) (N n :*: g) | f == g  = N (m + n) :*: f
simplSum f (g :+: h) | g < f                  = simplSum g (simplSum f h)
simplSum f g | g < f                           = g :+: f
simplSum f g                                   = f :+: g

simplProd :: SpeciesAST -> SpeciesAST -> SpeciesAST
simplProd Zero _              = Zero
simplProd _ Zero              = Zero
simplProd One g               = g
simplProd f One               = f
simplProd (N m) (N n)        = N $ m * n
simplProd (f1 :+: f2) g       = simplSum (simplProd f1 g) (simplProd f2 g)
simplProd f (g1 :+: g2)       = simplSum (simplProd f g1) (simplProd f g2)
simplProd f (N n)             = simplProd (N n) f
simplProd (N m) (N n :*: g) = simplProd (N $ m * n) g
simplProd f ((N n) :*: g)    = simplProd (N n) (simplProd f g)
simplProd (f :*: g) h         = simplProd f (simplProd g h)
simplProd f (g :*: h) | g < f = simplProd g (simplProd f h)
simplProd f g | g < f          = g :*: f
simplProd f g                  = f :*: g

simplComp :: SpeciesAST -> SpeciesAST -> SpeciesAST
simplComp Zero _        = Zero
simplComp One _         = One
simplComp (N n) _       = N n
simplComp X g           = g
simplComp f X           = f
simplComp f Zero        = simplOfSizeExactly f 0
simplComp (f1 :+: f2) g = simplSum (simplComp f1 g) (simplComp f2 g)
simplComp (f1 :*: f2) g = simplProd (simplComp f1 g) (simplComp f2 g)
simplComp (f :.: g) h   = f :.: (g :.: h)
simplComp f g            = f :.: g

simplCart :: SpeciesAST -> SpeciesAST -> SpeciesAST
simplCart f g = f :><: g  -- XXX

simplFunc :: SpeciesAST -> SpeciesAST -> SpeciesAST
simplFunc f g = f :@: g  -- XXX

simplDer :: SpeciesAST -> SpeciesAST
simplDer Zero      = Zero
simplDer One       = Zero
simplDer (N _)     = Zero
simplDer X         = One
simplDer E         = E
simplDer C         = L
simplDer L         = L :*: L
simplDer (f :+: g) = simplSum (simplDer f) (simplDer g)
simplDer (f :*: g) = simplSum (simplProd f (simplDer g)) (simplProd (simplDer f) g)
simplDer (f :.: g) = simplProd (simplComp (simplDer f) g) (simplDer g)
simplDer f          = Der f

simplOfSize :: SpeciesAST -> (Integer -> Bool) -> SpeciesAST
simplOfSize f p = OfSize f p  -- XXX

simplOfSizeExactly :: SpeciesAST -> Integer -> SpeciesAST
simplOfSizeExactly Zero _ = Zero
simplOfSizeExactly One 0 = One
simplOfSizeExactly One _ = Zero
simplOfSizeExactly (N n) 0 = N n
simplOfSizeExactly (N _) _ = Zero
simplOfSizeExactly X 1 = X
simplOfSizeExactly X _ = Zero
simplOfSizeExactly E 0 = One
simplOfSizeExactly C 0 = Zero
simplOfSizeExactly L 0 = One
simplOfSizeExactly (f :+: g) k = simplSum (simplOfSizeExactly f k) (simplOfSizeExactly g k)
simplOfSizeExactly (f :*: g) k = foldr simplSum Zero
                                    [ simplProd (simplOfSizeExactly f j) (simplOfSizeExactly g (k - j)) | j <- [0..k] ]

-- XXX get this to work?
--
-- Note, it's incorrect to multiply by f.  For regular f we can just
-- multiply together all the g's.  However for non-regular f this
-- doesn't work.  Seems difficult to do this properly...

-- simplOfSizeExactly (f :.: g) k = foldr simplSum Zero $
--                                     map (\gs -> simplProd (simplOfSizeExactly f (genericLength gs)) (foldr simplProd One gs))
--                                     [ map (simplOfSizeExactly g) p | p <- intPartitions k ]

simplOfSizeExactly f k = OfSizeExactly f k

simplNonEmpty :: SpeciesAST -> SpeciesAST
simplNonEmpty f = NonEmpty f  -- XXX

intPartitions :: Integer -> [[Integer]]
intPartitions k = intPartitions' k k
  -- intPartitions' k j gives partitions of k into parts of size at most j
  where intPartitions' 0 _ = [[]]
        intPartitions' k 1 = [replicate (fromInteger k) 1]
        intPartitions' k j = map (j:) (intPartitions' (k - j) (min (k-j) j))
                          ++ intPartitions' k (j-1)

-- | Simplify a species and decompose it into a sum of products.
sumOfProducts :: SpeciesAST -> [[SpeciesAST]]
sumOfProducts = terms . simplify
  where terms (f :+: g)   = factors f : terms g
        terms f            = [factors f]
        factors (f :*: g) = f : factors g
        factors f          = [f]