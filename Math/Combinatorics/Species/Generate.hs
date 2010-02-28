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
    , generateTyped
    , structureType

    , Iso(..), generate

    ) where

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Types
import Math.Combinatorics.Species.AST
import Math.Combinatorics.Species.Structures

import qualified Math.Combinatorics.Multiset as MS
import Math.Combinatorics.Multiset (Multiset(..), (+:))

import Data.Maybe (fromJust)

import Data.Typeable

import NumericPrelude
import PreludeBase hiding (cycle)

-- | Given an AST describing a species, with a phantom type parameter
--   representing the structure of the species, and an underlying
--   multiset of elements, generate a list of all possible structures
--   built over the underlying multiset.  (Of course, it would be
--   really nice to have a real dependently-typed language for this!)
--
--   Unfortunately, 'SpeciesAST' cannot be made an instance of
--   'Species', so if we want to be able to generate structures given
--   an expression of the 'Species' DSL as input, we must take
--   'ESpeciesAST' as input, which existentially wraps the phantom
--   structure type---but this means that the output list type must be
--   existentially quantified as well; see 'generate' and
--   'generateTyped' below.
--
--   Generating structures over base elements from a /multiset/
--   unifies labelled and unlabelled generation into one framework.
--   To generate labelled structures, use a multiset where each
--   element occurs exactly once; to generate unlabelled structures,
--   use a multiset with the desired number of copies of a single
--   element.  To do labelled generation we could get away without the
--   generality of multisets, but to do unlabelled generation we need
--   the full generality anyway.
generateT :: SpeciesAST s -> Multiset a -> [s a]
generateT (N n) (MS [])        = map Const [1..n]
generateT (N _) _              = []
generateT X (MS [(x,1)])       = [Id x]
generateT X _                  = []
generateT E xs                 = [Set (MS.toList xs)]
generateT C m                  = map Cycle (MS.cycles m)
generateT L xs                 = MS.permutations xs
generateT Subset xs            = map (Set . MS.toList . fst) (MS.splits xs)
generateT (KSubset k) xs       = map (Set . MS.toList)
                                     (MS.kSubsets (fromIntegral k) xs)
generateT Elt xs               = map (Id . fst) . MS.toCounts $ xs
generateT (f :+: g) xs         = map Inl (generateT f xs)
                              ++ map Inr (generateT g xs)
generateT (f :*: g) xs         = [ Prod x y
                                 | (s1,s2) <- MS.splits xs
                                 ,       x <- generateT f s1
                                 ,       y <- generateT g s2
                                 ]
generateT (f :.: g) xs         = [ Comp y
                                 | p   <- MS.partitions xs
                                 , xs' <- MS.sequenceMS . fmap (generateT g) $ p
                                 , y   <- generateT f xs'
                                 ]
generateT (f :><: g) xs        = [ Prod x y
                                 | x <- generateT f xs
                                 , y <- generateT g xs
                                 ]
generateT (f :@: g) xs         = map Comp
                                 . generateT f
                                 . MS.fromDistinctList
                                 . generateT g
                                 $ xs
generateT (Der f) xs           = map Comp
                                 . generateT f
                                 $ (Star,1) +: fmap Original xs
generateT (NonEmpty f) (MS []) = []
generateT (NonEmpty f) xs      = generateT f xs
generateT (Rec f) xs           = map Mu $ generateT (apply f (Rec f)) xs
generateT (OfSize f p) xs
  | p (fromIntegral . sum . MS.getCounts $ xs)
    = generateT f xs
  | otherwise = []
generateT (OfSizeExactly f n) xs
  | (fromIntegral . sum . MS.getCounts $ xs) == n
    = generateT f xs
  | otherwise = []

-- | An existential wrapper for structures, ensuring that the
--   structure functor results in something Showable and Typeable (when
--   applied to a Showable and Typeable argument type).
data Structure a where
  Structure :: Typeable1 f => f a -> Structure a

-- | Extract the contents from a 'Structure' wrapper, if we know the
--   type.
extractStructure :: (Typeable1 f, Typeable a) => Structure a -> Maybe (f a)
extractStructure (Structure s) = cast s

-- XXX change this comment
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

-- |  XXX comment me
generateS :: ESpeciesAST -> [a] -> [Structure a]
generateS (SA s) xs = map Structure (generateT s (MS.fromDistinctList xs))

-- XXX move this comment + edit?
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
  case (mapM extractStructure . generateS s $ xs) of
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

-- XXX better name for this class?
instance Iso Set where
  type SType Set = Set
  iso = id

-- XXX comment me, and better error handling
generate :: (Iso f, Typeable a) => ESpeciesAST -> [a] -> [f a]
generate s = fromJust . fmap (map iso) . mapM extractStructure . generateS s

-- XXX add a generateU function with Iso constraint for unlabelled generation


-- Old code for doing only labelled generation:
--
-- generateT :: SpeciesAST s -> [a] -> [s a]
-- generateT (N n) []       = map Const [1..n]
-- generateT (N _) _        = []
-- generateT X [x]          = [Id x]
-- generateT X _            = []
-- generateT E xs           = [Set xs]
-- generateT C []           = []
-- generateT C (x:xs)       = map (Cycle . (x:)) (sPermutations xs)
-- generateT L xs           = sPermutations xs
-- generateT Subset xs      = map (Set . fst) (pSet xs)
-- generateT (KSubset k) xs = map Set (sKSubsets k xs)
-- generateT Elt xs         = map Id xs
-- generateT (f :+: g) xs   = map Inl (generateT f xs)
--                         ++ map Inr (generateT g xs)
-- generateT (f :*: g) xs   = [ Prod x y | (s1,s2) <- pSet xs
--                                       ,       x <- generateT f s1
--                                       ,       y <- generateT g s2
--                            ]
-- generateT (f :.: g) xs   = [ Comp y | p   <- sPartitions xs
--                                     , xs' <- mapM (generateT g) p
--                                     , y   <- generateT f xs'
--                            ]
-- generateT (f :><: g) xs  = [ Prod x y | x <- generateT f xs
--                                       , y <- generateT g xs ]
-- generateT (f :@: g) xs   = map Comp $ generateT f (generateT g xs)
-- generateT (Der f) xs     = map Comp $ generateT f (Star : map Original xs)

-- generateT (OfSize f p) xs | p (genericLength xs) = generateT f xs
--                           | otherwise     = []
-- generateT (OfSizeExactly f n) xs | genericLength xs == n = generateT f xs
--                                  | otherwise = []
-- generateT (NonEmpty f) [] = []
-- generateT (NonEmpty f) xs = generateT f xs
-- generateT (Rec f) xs = map Mu $ generateT (apply f (Rec f)) xs
--
-- -- | @pSet xs@ generates the power set of @xs@, yielding a list of
-- --   subsets of @xs@ paired with their complements.
-- pSet :: [a] -> [([a],[a])]
-- pSet [] = [([],[])]
-- pSet (x:xs) = mapx first ++ mapx second
--   where mapx which = map (which (x:)) $ pSet xs
--
-- -- | @sKSubsets k xs@ generate all the size-k subsets of @xs@.
-- sKSubsets :: Integer -> [a] -> [[a]]
-- sKSubsets 0 _      = [[]]
-- sKSubsets _ []     = []
-- sKSubsets n (x:xs) = map (x:) (sKSubsets (n-1) xs) ++ sKSubsets n xs
--
-- -- | Generate all partitions of a set.
-- sPartitions :: [a] -> [[[a]]]
-- sPartitions [] = [[]]
-- sPartitions (s:s') = do (sub,compl) <- pSet s'
--                         let firstSubset = s:sub
--                         map (firstSubset:) $ sPartitions compl
--
-- -- | Generate all permutations of a list.
-- sPermutations :: [a] -> [[a]]
-- sPermutations [] = [[]]
-- sPermutations xs = [ y:p | (y,ys) <- select xs
--                          , p      <- sPermutations ys
--                    ]
--
-- -- | Select each element of a list in turn, yielding a list of
-- --   elements, each paired with a list of the remaining elements.
-- select :: [a] -> [(a,[a])]
-- select [] = []
-- select (x:xs) = (x,xs) : map (second (x:)) (select xs)


