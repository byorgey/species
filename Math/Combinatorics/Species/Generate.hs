{-# LANGUAGE NoImplicitPrelude
           , GADTs
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , ScopedTypeVariables
           , KindSignatures
           , TypeFamilies
           , DeriveDataTypeable
  #-}

-- | Generation of species: given a species and an underlying set of
--   labels, generate a list of all structures built from the
--   underlying set.
module Math.Combinatorics.Species.Generate
    ( generateT
    , Structure(..)
    , generate
    , generateTyped
    , structureType

    , Iso(..), generateI

    , generateTU

    ) where

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Types
import Math.Combinatorics.Species.AST
import Math.Combinatorics.Species.CycleIndex (intPartitions)
import Math.Combinatorics.Species.Structures

import Control.Arrow (first, second)
import Data.List (genericLength, genericReplicate)
import Data.Maybe (fromJust)

import Data.Typeable

import NumericPrelude
import PreludeBase hiding (cycle)

-- | Given an AST describing a species, with a phantom type parameter
--   representing the structure of the species, and an underlying set,
--   generate a list of all possible structures built over the
--   underlying set.  (Of course, it would be really nice to have a
--   real dependently-typed language for this!)
--
--   Unfortunately, 'SpeciesAST' cannot be made an instance of
--   'Species', so if we want to be able to generate structures given
--   an expression of the 'Species' DSL as input, we must take
--   'ESpeciesAST' as input, which existentially wraps the phantom
--   structure type---but this means that the output list type must be
--   existentially quantified as well; see 'generate' and
--   'generateTyped' below.
generateT :: SpeciesAST s -> [a] -> [s a]
generateT (N n) []       = map Const [1..n]
generateT (N _) _        = []
generateT X [x]          = [Id x]
generateT X _            = []
generateT E xs           = [Set xs]
generateT C []           = []
generateT C (x:xs)       = map (Cycle . (x:)) (sPermutations xs)
generateT L xs           = sPermutations xs
generateT Subset xs      = map (Set . fst) (pSet xs)
generateT (KSubset k) xs = map Set (sKSubsets k xs)
generateT Elt xs         = map Id xs
generateT (f :+: g) xs   = map Inl (generateT f xs)
                        ++ map Inr (generateT g xs)
generateT (f :*: g) xs   = [ Prod x y | (s1,s2) <- pSet xs
                                      ,       x <- generateT f s1
                                      ,       y <- generateT g s2
                           ]
generateT (f :.: g) xs   = [ Comp y | p  <- sPartitions xs
                                    , xs <- mapM (generateT g) p
                                    , y  <- generateT f xs
                           ]
generateT (f :><: g) xs  = [ Prod x y | x <- generateT f xs
                                      , y <- generateT g xs ]
generateT (f :@: g) xs   = map Comp $ generateT f (generateT g xs)
generateT (Der f) xs     = map Comp $ generateT f (Star : map Original xs)

generateT (OfSize f p) xs | p (genericLength xs) = generateT f xs
                          | otherwise     = []
generateT (OfSizeExactly f n) xs | genericLength xs == n = generateT f xs
                                 | otherwise = []
generateT (NonEmpty f) [] = []
generateT (NonEmpty f) xs = generateT f xs
generateT (Rec f) xs = map Mu $ generateT (apply f (Rec f)) xs

-- | @pSet xs@ generates the power set of @xs@, yielding a list of
--   subsets of @xs@ paired with their complements.
pSet :: [a] -> [([a],[a])]
pSet [] = [([],[])]
pSet (x:xs) = mapx first ++ mapx second
  where mapx which = map (which (x:)) $ pSet xs

-- | @sKSubsets k xs@ generate all the size-k subsets of @xs@.
sKSubsets :: Integer -> [a] -> [[a]]
sKSubsets 0 _      = [[]]
sKSubsets _ []     = []
sKSubsets n (x:xs) = map (x:) (sKSubsets (n-1) xs) ++ sKSubsets n xs

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

-- | An existential wrapper for structures, ensuring that the
--   structure functor results in something Showable and Typeable (when
--   applied to a Showable and Typeable argument type).
data Structure a where
  Structure :: Typeable1 f => f a -> Structure a

extractStructure :: (Typeable1 f, Typeable a) => Structure a -> Maybe (f a)
extractStructure (Structure s) = cast s

-- | @generate s ls@ generates a complete list of all s-structures
--   over the underlying set of labels @ls@.  For example:
--
-- > > generate octopi ([1,2,3] :: [Int])
-- > [<[1,2,3]>,<[1,3,2]>,<[2,1,3]>,<[2,3,1]>,<[3,1,2]>,<[3,2,1]>,<[1,2],[3]>,
-- >  <[2,1],[3]>,<[1,3],[2]>,<[3,1],[2]>,<[1],[2,3]>,<[1],[3,2]>,<[1],[2],[3]>,
-- >  <[1],[3],[2]>]
-- >
-- > > generate subsets "abc"
-- > [{'a','b','c'},{'a','b'},{'a','c'},{'a'},{'b','c'},{'b'},{'c'},{}]
--
-- > > generate simpleGraphs ([1,2,3] :: [Int])
-- > [{{1,2},{1,3},{2,3}},{{1,2},{1,3}},{{1,2},{2,3}},{{1,2}},{{1,3},{2,3}},
-- >  {{1,3}},{{2,3}},{}]
--
--   There is one caveat: since the type of the generated structures
--   is different for each species, it must be existentially
--   quantified!  The output of 'generate' can always be Shown, but
--   not much else.
--
--   However!  All is not lost.  It's possible, by the magic of
--   "Data.Typeable", to yank the type information (kicking and
--   screaming) back into the open, so that you can then manipulate
--   the generated structures to your heart's content.  To see how,
--   consult 'structureType' and 'generateTyped'.
generate :: ESpeciesAST -> [a] -> [Structure a]
generate (SA s) xs = map Structure (generateT s xs)

-- | @generateTyped s ls@ generates a complete list of all s-structures
--   over the underlying set of labels @ls@, where the type of the
--   generated structures is known ('structureType' may be used to
--   compute this type).  For example:
--
-- > > structureType subsets
-- > "Set"
-- > > generateTyped subsets ([1,2,3] :: [Int]) :: [Set Int]
-- > [{1,2,3},{1,2},{1,3},{1},{2,3},{2},{3},{}]
-- > > map (sum . getSet) $ it
-- > [6,3,4,1,5,2,3,0]
--
--   Although the output from 'generate' appears the same, trying to
--   compute the subset sums fails spectacularly if we use 'generate'
--   instead of 'generateTyped':
--
-- > > generate subsets ([1..3] :: [Int])
-- > [{1,2,3},{1,2},{1,3},{1},{2,3},{2},{3},{}]
-- > > map (sum . getSet) $ it
-- > <interactive>:1:21:
-- >     Couldn't match expected type `Set a'
-- >            against inferred type `Math.Combinatorics.Species.Generate.Structure
-- >                                     Int'
-- >       Expected type: [Set a]
-- >       Inferred type: [Math.Combinatorics.Species.Generate.Structure Int]
-- >     In the second argument of `($)', namely `it'
-- >     In the expression: map (sum . getSet) $ it
--
--   If we use the wrong type, we get a nice error message:
--
-- > > generateTyped octopi ([1..3] :: [Int]) :: [Set Int]
-- > *** Exception: structure type mismatch.
-- >   Expected: Set Int
-- >   Inferred: Comp Cycle (Comp Cycle Star) Int
generateTyped :: forall f a. (Typeable1 f, Typeable a) => ESpeciesAST -> [a] -> [f a]
generateTyped s xs =
  case (mapM extractStructure . generate s $ xs) of
    Nothing -> error $
          "structure type mismatch.\n"
       ++ "  Expected: " ++ showStructureType (typeOf (undefined :: f a)) ++ "\n"
       ++ "  Inferred: " ++ structureType s ++ " " ++ show (typeOf (undefined :: a))
    Just ys -> ys

-- | @'structureType' s@ returns a String representation of the
--   functor type which represents the structure of the species @s@.
--   In particular, if @structureType s@ prints @\"T\"@, then you can
--   safely use 'generateTyped' by writing
--
-- > generateTyped s ls :: [T L]
--
--   where @ls :: [L]@.
structureType :: ESpeciesAST -> String
structureType (SA s) = showStructureType . extractType $ s
  where extractType :: forall s. Typeable1 s => SpeciesAST s -> TypeRep
        extractType _ = typeOf1 (undefined :: s ())

-- | Show a TypeRep while stripping off qualifier portions of TyCon
--   names.  This is essentially copied and pasted from the
--   Data.Typeable source, with a number of cases taken out that we
--   don't care about (special cases for (->), tuples, etc.).
showStructureType :: TypeRep -> String
showStructureType t = showsPrecST 0 t ""
  where showsPrecST :: Int -> TypeRep -> ShowS
        showsPrecST p t =
          case splitTyConApp t of
            (tycon, [])   -> showString (dropQuals $ tyConString tycon)
            (tycon, [x])  | tyConString tycon == "[]"
                          -> showChar '[' . showsPrecST 11 x . showChar ']'
            (tycon, args) -> showParen (p > 9)
                           $ showString (dropQuals $ tyConString tycon)
                           . showChar ' '
                           . showArgsST args

        showArgsST :: [TypeRep] -> ShowS
        showArgsST []     = id
        showArgsST [t]    = showsPrecST 10 t
        showArgsST (t:ts) = showsPrecST 10 t . showChar ' ' . showArgsST ts

        dropQuals :: String -> String
        dropQuals = reverse . takeWhile (/= '.') . reverse


-- XXX comment me

class Typeable1 (SType f) => Iso (f :: * -> *) where
  type SType f :: * -> *
  iso :: SType f a -> f a

generateI :: (Iso f, Typeable a) => ESpeciesAST -> [a] -> [f a]
generateI s = fromJust . fmap (map iso) . mapM extractStructure . generate s

-- More old code below: a first try at *unlabelled* generation, but
-- it's not quite so easy---for exactly the same reasons that ordinary
-- generating function composition/derivative etc. don't correspond to
-- species operations.

-- | Given an AST describing a *regular* species, with a phantom type
--   parameter representing the structure of the species, and the size
--   of the underlying set, generate a list of all possible unlabelled
--   structures built by the species.
generateTU :: SpeciesAST s -> Integer -> [s ()]
generateTU (N _) 0  = [Const 1]
generateTU (N _) _  = []
generateTU X 1  = [Id ()]
generateTU X _  = []
generateTU (f :+: g) n = map Inl (generateTU f n)
                      ++ map Inr (generateTU g n)
generateTU (f :*: g) n = [ Prod x y | n1 <- [0..n]
                                    , x  <- generateTU f n1
                                    , y  <- generateTU g (n - n1)
                         ]
generateTU (f :.: g) n = [ Comp y | p  <- intPartitions n
                                  , xs <- mapM (generateTU g) $ expandPartition p
                                  , y  <- generateT f xs
                         ]
-- generateTU (Der f) n = map    -- XXX how to do this?
-- generateTU E n = [Set $ genericReplicate n ()]
-- generateTU C 0 = []
-- generateTU C n = [Cycle $ genericReplicate n ()]
generateTU L n = [genericReplicate n ()]
generateTU (OfSize f p) n | p n = generateTU f n
                          | otherwise = []
generateTU (OfSizeExactly f s) n | s == n = generateTU f n
                                 | otherwise = []
generateTU (NonEmpty f) n | n > 0 = generateTU f n
                          | otherwise = []
generateTU (f :><: g) n = [ Prod x y | x <- generateTU f n
                                     , y <- generateTU g n
                          ]
generateTU (Rec f) n = map Mu $ generateTU (apply f (Rec f)) n

expandPartition :: [(Integer, Integer)] -> [Integer]
expandPartition = concatMap (uncurry (flip genericReplicate))

