{-# LANGUAGE NoImplicitPrelude 
           , GADTs
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
  #-}
module Math.Combinatorics.Species.Generate where

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Types
import Math.Combinatorics.Species.Algebra

import Control.Arrow (first, second)

import NumericPrelude
import PreludeBase hiding (cycle)

generateF :: SpeciesAlgT s -> [a] -> [StructureF s a]
generateF O _   = []
generateF I []  = [Const 1]
generateF I _   = []
generateF X [x] = [Identity x]
generateF X _   = []
generateF (f :+: g) xs = map (Sum . Left ) (generateF f xs) 
                      ++ map (Sum . Right) (generateF g xs)
generateF (f :*: g) xs = [ Prod (x, y) | (s1,s2) <- splits xs
                                       ,       x <- generateF f s1
                                       ,       y <- generateF g s2
                         ]
generateF (f :.: g) xs = [ Comp y | p  <- sPartitions xs
                                  , xs <- mapM (generateF g) p
                                  , y  <- generateF f xs
                         ]
generateF (Der f) xs = map Comp $ generateF f (Star : map Original xs)
generateF E xs = [xs]
generateF C [] = []
generateF C (x:xs) = map (Cycle . (x:)) (permutations xs)
generateF (NonEmpty f) [] = []
generateF (NonEmpty f) xs = generateF f xs

-- power set
pSet :: [a] -> [([a],[a])]
pSet [] = [([],[])]
pSet (x:xs) = mapx first ++ mapx second 
  where mapx which = map (which (x:)) $ pSet xs

sPartitions :: [a] -> [[[a]]]
sPartitions [] = [[]]
sPartitions (s:s') = do (sub,compl) <- pSet s'
                        let firstSubset = s:sub
                        map (firstSubset:) $ sPartitions compl

splits :: [a] -> [([a],[a])]
splits []     = [([],[])]
splits (x:xs) = map (first (x:)) ss ++ map (second (x:)) ss
  where ss = splits xs

permutations :: [a] -> [[a]]
permutations [] = [[]]
permutations xs = [ y:p | (y,ys) <- select xs
                        , p      <- permutations ys
                  ]

select :: [a] -> [(a,[a])]
select [] = []
select (x:xs) = (x,xs) : map (second (x:)) (select xs)


data Structure a where
  Structure :: (ShowF f) => f a -> Structure a

instance (Show a) => Show (Structure a) where
  show (Structure t) = showF t

generate :: SpeciesAlg -> [a] -> [Structure a]
generate (SA s) xs = map Structure (generateF s xs)

class Iso f g where
  iso :: f a -> g a

instance Iso (Comp Cycle Star) [] where
  iso (Comp (Cycle (_:xs))) = map (\(Original x) -> x) xs

instance (Iso f g, Functor h) => Iso (Comp h f) (Comp h g) where
  iso (Comp h) = Comp (fmap iso h)

instance (Iso f1 f2, Iso g1 g2) => Iso (Sum f1 g1) (Sum f2 g2) where
  iso (Sum (Left x)) = Sum (Left (iso x))
  iso (Sum (Right x)) = Sum (Right (iso x))

instance (Iso f1 f2, Iso g1 g2) => Iso (Prod f1 g1) (Prod f2 g2) where
  iso (Prod (x,y)) = Prod (iso x, iso y)

generateFI :: (Iso (StructureF s) f) => SpeciesAlgT s -> [a] -> [f a]
generateFI s xs = map iso $ generateF s xs
