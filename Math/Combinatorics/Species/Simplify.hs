{-# LANGUAGE NoImplicitPrelude, GADTs #-}

-- | Functions to manipulate and simplify species expressions
--   according to algebraic species isomorphisms.
module Math.Combinatorics.Species.Simplify
    ( simplify, sumOfProducts
    ) where

import NumericPrelude
import PreludeBase

import Math.Combinatorics.Species
import Math.Combinatorics.Species.AST

import Data.List (genericLength)
import Data.Typeable

simplify :: USpeciesAST -> USpeciesAST
simplify UZero          = UZero
simplify UOne           = UOne
simplify (UN 0)         = UZero
simplify (UN 1)         = UOne
simplify f@(UN _)       = f
simplify UX             =  UX
simplify UE             =  UE
simplify UC             =  UC
simplify UL             =  UL
simplify USubset        =  USubset
simplify f@(UKSubset _) =  f
simplify UElt           =  UElt
simplify (f :+:% g)     = simplSum (simplify f) (simplify g)
simplify (f :*:% g)     = simplProd (simplify f) (simplify g)
simplify (f :.:% g)     = simplComp (simplify f) (simplify g)
simplify (f :><:% g)    = simplCart (simplify f) (simplify g)
simplify (f :@:% g)     = simplFunc (simplify f) (simplify g)
simplify (UDer f)       = simplDer (simplify f)
simplify (UOfSize f p)  = simplOfSize (simplify f) p
simplify (UOfSizeExactly f k) = simplOfSizeExactly (simplify f) k
simplify (UNonEmpty f)  = simplNonEmpty (simplify f)
simplify (URec f)       = URec f
simplify UOmega         = UOmega

simplSum :: USpeciesAST -> USpeciesAST -> USpeciesAST
simplSum UZero g                               = g
simplSum f UZero                               = f
simplSum UOne UOne                             = UN 2
simplSum UOne (UN n)                           = UN $ succ n
simplSum (UN n) UOne                           = UN $ succ n
simplSum (UN m) (UN n)                         = UN $ m + n
simplSum UOne (UOne :+:% g)                    = simplSum (UN 2) g
simplSum UOne ((UN n) :+:% g)                  = simplSum (UN $ succ n) g
simplSum (UN n) (UOne :+:% g)                  = simplSum (UN $ succ n) g
simplSum (UN m) ((UN n) :+:% g)                = simplSum (UN (m + n)) g
simplSum (f :+:% g) h                          = simplSum f (simplSum g h)
simplSum f g | f == g                          = simplProd (UN 2) f
simplSum f (g :+:% h) | f == g                 = simplSum (simplProd (UN 2) f) h
simplSum (UN n :*:% f) g | f == g              = UN (succ n) :*:% f
simplSum f (UN n :*:% g) | f == g              = UN (succ n) :*:% f
simplSum (UN m :*:% f) (UN n :*:% g) | f == g  = UN (m + n) :*:% f
simplSum f (g :+:% h) | g < f                  = simplSum g (simplSum f h)
simplSum f g | g < f                           = g :+:% f
simplSum f g                                   = f :+:% g

simplProd :: USpeciesAST -> USpeciesAST -> USpeciesAST
simplProd UZero _              = UZero
simplProd _ UZero              = UZero
simplProd UOne g               = g
simplProd f UOne               = f
simplProd (UN m) (UN n)        = UN $ m * n
simplProd (f1 :+:% f2) g       = simplSum (simplProd f1 g) (simplProd f2 g)
simplProd f (g1 :+:% g2)       = simplSum (simplProd f g1) (simplProd f g2)
simplProd f (UN n)             = simplProd (UN n) f
simplProd (UN m) (UN n :*:% g) = simplProd (UN $ m * n) g
simplProd f ((UN n) :*:% g)    = simplProd (UN n) (simplProd f g)
simplProd (f :*:% g) h         = simplProd f (simplProd g h)
simplProd f (g :*:% h) | g < f = simplProd g (simplProd f h)
simplProd f g | g < f          = g :*:% f
simplProd f g                  = f :*:% g

simplComp :: USpeciesAST -> USpeciesAST -> USpeciesAST
simplComp UZero _        = UZero
simplComp UOne _         = UOne
simplComp (UN n) _       = UN n
simplComp UX g           = g
simplComp f UX           = f
simplComp f UZero        = simplOfSizeExactly f 0
simplComp (f1 :+:% f2) g = simplSum (simplComp f1 g) (simplComp f2 g)
simplComp (f1 :*:% f2) g = simplProd (simplComp f1 g) (simplComp f2 g)
simplComp (f :.:% g) h   = f :.:% (g :.:% h)
simplComp f g            = f :.:% g

simplCart :: USpeciesAST -> USpeciesAST -> USpeciesAST
simplCart f g = f :><:% g  -- XXX

simplFunc :: USpeciesAST -> USpeciesAST -> USpeciesAST
simplFunc f g = f :@:% g  -- XXX

simplDer :: USpeciesAST -> USpeciesAST
simplDer UZero      = UZero
simplDer UOne       = UZero
simplDer (UN _)     = UZero
simplDer UX         = UOne
simplDer UE         = UE
simplDer UC         = UL
simplDer UL         = UL :*:% UL
simplDer (f :+:% g) = simplSum (simplDer f) (simplDer g)
simplDer (f :*:% g) = simplSum (simplProd f (simplDer g)) (simplProd (simplDer f) g)
simplDer (f :.:% g) = simplProd (simplComp (simplDer f) g) (simplDer g)
simplDer f          = UDer f

simplOfSize :: USpeciesAST -> (Integer -> Bool) -> USpeciesAST
simplOfSize f p = UOfSize f p  -- XXX

simplOfSizeExactly :: USpeciesAST -> Integer -> USpeciesAST
simplOfSizeExactly UZero _ = UZero
simplOfSizeExactly UOne 0 = UOne
simplOfSizeExactly UOne _ = UZero
simplOfSizeExactly (UN n) 0 = UN n
simplOfSizeExactly (UN _) _ = UZero
simplOfSizeExactly UX 1 = UX
simplOfSizeExactly UX _ = UZero
simplOfSizeExactly UE 0 = UOne
simplOfSizeExactly UC 0 = UZero
simplOfSizeExactly UL 0 = UOne
simplOfSizeExactly (f :+:% g) k = simplSum (simplOfSizeExactly f k) (simplOfSizeExactly g k)
simplOfSizeExactly (f :*:% g) k = foldr simplSum UZero
                                    [ simplProd (simplOfSizeExactly f j) (simplOfSizeExactly g (k - j)) | j <- [0..k] ]

-- XXX get this to work?
--
-- Note, it's incorrect to multiply by f.  For regular f we can just
-- multiply together all the g's.  However for non-regular f this
-- doesn't work.  Seems difficult to do this properly...

-- simplOfSizeExactly (f :.:% g) k = foldr simplSum UZero $
--                                     map (\gs -> simplProd (simplOfSizeExactly f (genericLength gs)) (foldr simplProd UOne gs))
--                                     [ map (simplOfSizeExactly g) p | p <- intPartitions k ]

simplOfSizeExactly f k = UOfSizeExactly f k

simplNonEmpty :: USpeciesAST -> USpeciesAST
simplNonEmpty f = UNonEmpty f  -- XXX

intPartitions :: Integer -> [[Integer]]
intPartitions k = intPartitions' k k
  -- intPartitions' k j gives partitions of k into parts of size at most j
  where intPartitions' 0 _ = [[]]
        intPartitions' k 1 = [replicate (fromInteger k) 1]
        intPartitions' k j = map (j:) (intPartitions' (k - j) (min (k-j) j))
                          ++ intPartitions' k (j-1)

-- | Simplify a species and decompose it into a sum of products.
sumOfProducts :: USpeciesAST -> [[USpeciesAST]]
sumOfProducts = terms . simplify
  where terms (f :+:% g)   = factors f : terms g
        terms f            = [factors f]
        factors (f :*:% g) = f : factors g
        factors f          = [f]