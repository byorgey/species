{-# LANGUAGE NoImplicitPrelude 
           , GADTs
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
  #-}

-- | Generation of species: given a species and an underlying set of
--   labels, generate a list of all structures built from the
--   underlying set.
module Math.Combinatorics.Species.Generate
    ( generateF
    , Structure(..)
    , generate
    , generate'
    , structureType

    ) where

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Types
import Math.Combinatorics.Species.Algebra
import Math.Combinatorics.Species.CycleIndex (intPartitions)

import Control.Arrow (first, second)
import Data.List (genericLength, genericReplicate)

import Data.Typeable

import NumericPrelude
import PreludeBase hiding (cycle)

-- | Given an AST describing a species, with a phantom type parameter
--   describing the species at the type level, and an underlying set,
--   generate a list of all possible structures built over the
--   underlying set.  Of course, the type of the output list is a
--   function of the species structure.  (Of course, it would be
--   really nice to have a real dependently-typed language for this!)
--
--   Unfortunately, 'SpeciesAlgT' cannot be made an instance of
--   'Species', so if we want to be able to generate structures given
--   an expression of the 'Species' DSL as input, we must take
--   'SpeciesAlg' as input, which existentially wraps the phantom
--   structure type---but this means that the output list type must be
--   existentially quantified as well; see 'generate' below.
generateF :: SpeciesAlgT s -> [a] -> [StructureF s a]
generateF O _           = []
generateF I []          = [Const 1]
generateF I _           = []
generateF X [x]         = [Identity x]
generateF X _           = []
generateF E xs          = [Set xs]
generateF C []          = []
generateF C (x:xs)      = map (Cycle . (x:)) (sPermutations xs)
generateF (f :+: g) xs  = map (Sum . Left ) (generateF f xs) 
                        ++ map (Sum . Right) (generateF g xs)
generateF (f :*: g) xs  = [ Prod (x, y) | (s1,s2) <- pSet xs
                                        ,       x <- generateF f s1
                                        ,       y <- generateF g s2
                          ]
generateF (f :.: g) xs  = [ Comp y | p  <- sPartitions xs
                                   , xs <- mapM (generateF g) p
                                   , y  <- generateF f xs
                          ]
generateF (f :><: g) xs = [ Prod (x,y) | x <- generateF f xs
                                       , y <- generateF g xs ]
generateF (f :@: g) xs  = map Comp $ generateF f (generateF g xs)
generateF (Der f) xs    = map Comp $ generateF f (Star : map Original xs)

generateF (OfSize f p) xs | p (genericLength xs) = generateF f xs
                          | otherwise     = []
generateF (OfSizeExactly f n) xs | genericLength xs == n = generateF f xs
                                 | otherwise = []
generateF (f :><: g) xs = [ Prod (x,y) | x <- generateF f xs
                                       , y <- generateF g xs ]

-- | @pSet xs@ generates the power set of @xs@, yielding a list of
--   subsets of @xs@ paired with their complements.
pSet :: [a] -> [([a],[a])]
pSet [] = [([],[])]
pSet (x:xs) = mapx first ++ mapx second 
  where mapx which = map (which (x:)) $ pSet xs

-- | Generate all partitions of a set.
sPartitions :: [a] -> [[[a]]]
sPartitions [] = [[]]
sPartitions (s:s') = do (sub,compl) <- pSet s'
                        let firstSubset = s:sub
                        map (firstSubset:) $ sPartitions compl

-- | Generate all permutations of a list.
sPermutations :: [a] -> [[a]]
sPermutations [] = [[]]
sPermutations xs = [ y:p | (y,ys) <- select xs
                         , p      <- sPermutations ys
                  ]

-- | Select each element of a list in turn, yielding a list of
--   elements, each paired with a list of the remaining elements.
select :: [a] -> [(a,[a])]
select [] = []
select (x:xs) = (x,xs) : map (second (x:)) (select xs)

-- | An existential wrapper for structures.  For now we just ensure
--   that they are Showable; in a future version of the library I hope
--   to be able to add a Typeable constraint as well, so that we can
--   actually usefully recover the generated values if we know what
--   type we are expecting.
data Structure a where
  Structure :: (ShowF f, Typeable1 f, Functor f) => f a -> Structure a

instance (Show a) => Show (Structure a) where
  show (Structure t) = showF t

instance Functor Structure where
  fmap f (Structure fa) = Structure (fmap f fa)

extractStructure :: (Typeable1 f, Typeable a) => Structure a -> Maybe (f a)
extractStructure (Structure s) = cast s

-- | We can generate structures from a 'SpeciesAlg' (which is an
--   instance of 'Species') only if we existentially quantify over the
--   output type.  However, we have guaranteed that the structures
--   will be Showable.  For example:
--
-- > > generate octopi ([1,2,3] :: [Int])
-- > [{{*,1,2,3}},{{*,1,3,2}},{{*,2,1,3}},{{*,2,3,1}},{{*,3,1,2}},{{*,3,2,1}},
-- >  {{*,1,2},{*,3}},{{*,2,1},{*,3}},{{*,1,3},{*,2}},{{*,3,1},{*,2}},{{*,1},
-- >  {*,2,3}},{{*,1},{*,3,2}},{{*,1},{*,2},{*,3}},{{*,1},{*,3},{*,2}}]
--
-- Of course, this is not the output we might hope for; octopi are
-- cycles of lists, but above we are seeing the fact that lists are
-- implemented as the derivative of cycles, so each list is
-- represented by a cycle containing *.  In a future version of this
-- library I plan to implement a system for automatically converting
-- between isomorphic structures during species generation.
generate :: SpeciesAlg -> [a] -> [Structure a]
generate (SA s) xs = map Structure (generateF s xs)

generate' :: (Typeable1 f, Typeable a) => SpeciesAlg -> [a] -> [f a]
generate' s xs = case (mapM extractStructure . generate s $ xs) of
                   Nothing -> error "wrong structure type."
                   Just ys -> ys

-- Stuff for figuring out what type is generated by a species.
structureType :: SpeciesAlg -> String
structureType s = adjust . show . extractType $ generate s [()]
  where extractType []              = typeOf ()
        extractType (Structure x:_) = typeOf1 x
        adjust = unwords . map prune . words  -- XXX deal with parens.
        prune  = reverse . takeWhile (/= '.') . reverse

-- Experimental stuff below, automatically converting between
-- isomorphic structures.
--
-- class Iso f g where
--   iso :: f a -> g a

-- instance Iso (Comp Cycle Star) [] where
--   iso (Comp (Cycle (_:xs))) = map (\(Original x) -> x) xs

-- instance (Iso f g, Functor h) => Iso (Comp h f) (Comp h g) where
--   iso (Comp h) = Comp (fmap iso h)

-- instance (Iso f1 f2, Iso g1 g2) => Iso (Sum f1 g1) (Sum f2 g2) where
--   iso (Sum (Left x)) = Sum (Left (iso x))
--   iso (Sum (Right x)) = Sum (Right (iso x))

-- instance (Iso f1 f2, Iso g1 g2) => Iso (Prod f1 g1) (Prod f2 g2) where
--   iso (Prod (x,y)) = Prod (iso x, iso y)

-- generateFI :: (Iso (StructureF s) f) => SpeciesAlgT s -> [a] -> [f a]
-- generateFI s xs = map iso $ generateF s xs
