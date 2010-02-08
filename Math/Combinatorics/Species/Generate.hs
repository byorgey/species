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
    ( generateF
    , Structure(..)
    , generate
    , generateTyped
    , structureType

    , generateI

    ) where

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Types
import Math.Combinatorics.Species.AST
import Math.Combinatorics.Species.CycleIndex (intPartitions)

import Control.Arrow (first, second)
import Data.List (genericLength, genericReplicate)

import Data.Typeable

import NumericPrelude
import PreludeBase hiding (cycle)

-- | Given an AST describing a species, with a phantom type parameter
--   describing the species at the type level, and an underlying set,
--   generate a list of all possible structures built over the
--   underlying set; the type of the output list is a
--   function of the species structure.  (Of course, it would be
--   really nice to have a real dependently-typed language for this!)
--
--   Unfortunately, 'SpeciesTypedAST' cannot be made an instance of
--   'Species', so if we want to be able to generate structures given
--   an expression of the 'Species' DSL as input, we must take
--   'SpeciesAST' as input, which existentially wraps the phantom
--   structure type---but this means that the output list type must be
--   existentially quantified as well; see 'generate' and
--   'generateTyped' below.
generateF :: SpeciesTypedAST s -> [a] -> [s a]
generateF (N n) []       = map Const [1..n]
generateF (N _) _        = []
generateF X [x]          = [Identity x]
generateF X _            = []
generateF E xs           = [Set xs]
generateF C []           = []
generateF C (x:xs)       = map (Cycle . (x:)) (sPermutations xs)
generateF L xs           = sPermutations xs
generateF Subset xs      = map (Set . fst) (pSet xs)
generateF (KSubset k) xs = map Set (sKSubsets k xs)
generateF Elt xs         = map Identity xs
generateF (f :+: g) xs   = map (Sum . Left ) (generateF f xs)
                         ++ map (Sum . Right) (generateF g xs)
generateF (f :*: g) xs   = [ Prod (x, y) | (s1,s2) <- pSet xs
                                         ,       x <- generateF f s1
                                         ,       y <- generateF g s2
                           ]
generateF (f :.: g) xs   = [ Comp y | p  <- sPartitions xs
                                    , xs <- mapM (generateF g) p
                                    , y  <- generateF f xs
                           ]
generateF (f :><: g) xs  = [ Prod (x,y) | x <- generateF f xs
                                        , y <- generateF g xs ]
generateF (f :@: g) xs   = map Comp $ generateF f (generateF g xs)
generateF (Der f) xs     = map Comp $ generateF f (Star : map Original xs)

generateF (OfSize f p) xs | p (genericLength xs) = generateF f xs
                          | otherwise     = []
generateF (OfSizeExactly f n) xs | genericLength xs == n = generateF f xs
                                 | otherwise = []
generateF (NonEmpty f) [] = []
generateF (NonEmpty f) xs = generateF f xs
generateF (Rec f) xs = map Mu $ generateF (unfold f (Rec f)) xs

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
generate :: SpeciesAST -> [a] -> [Structure a]
generate (SA s) xs = map Structure (generateF s xs)

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
generateTyped :: forall f a. (Typeable1 f, Typeable a) => SpeciesAST -> [a] -> [f a]
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
structureType :: SpeciesAST -> String
structureType (SA s) = showStructureType . extractType $ s
  where extractType :: forall s. Typeable1 s => SpeciesTypedAST s -> TypeRep
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

generateI :: (Iso f, Typeable a) => SpeciesAST -> [a] -> Maybe [f a]
generateI s = fmap (map iso) . mapM extractStructure . generate s

data BinTree a = Empty | Node (BinTree a) a (BinTree a)
  deriving (Typeable)

instance Show a => Show (BinTree a) where
  show Empty = ""
  show (Node l a r) = "(" ++ show l ++ show a ++ show r ++ ")"

instance Iso BinTree where
  type SType BinTree = Mu BTree
  iso (Mu (Sum (Left _))) = Empty
  iso (Mu (Sum (Right (Prod (Identity a, Prod (l, r)))))) = Node (iso l) a (iso r)

-- More old code below: a first try at *unlabelled* generation, but
-- it's not quite so easy---for exactly the same reasons that ordinary
-- generating function composition/derivative etc. don't correspond to
-- species operations.

-- | Given an AST describing a species, with a phantom type parameter
--   describing the species at the type level, and the size of the
--   underlying set, generate a list of all possible unlabelled
--   structures built by the species.
-- generateFU :: SpeciesTypedAST s -> Integer -> [StructureF s ()]
-- generateFU O _  = []
-- generateFU I 0  = [Const 1]
-- generateFU I _  = []
-- generateFU X 1  = [Identity ()]
-- generateFU X _  = []
-- generateFU (f :+: g) n = map (Sum . Left ) (generateFU f n)
--                       ++ map (Sum . Right) (generateFU g n)
-- generateFU (f :*: g) n = [ Prod (x, y) | n1 <- [0..n]
--                                        , x  <- generateFU f n1
--                                        , y  <- generateFU g (n - n1)
--                          ]
-- generateFU (f :.: g) n = [ Comp y | p  <- intPartitions n
--                                   , xs <- mapM (generateFU g) $ expandPartition p
--                                   , y  <- generateF f xs
--                          ]
-- -- generateFU (Der f) n = map    -- XXX how to do this?
-- generateFU E n = [Set $ genericReplicate n ()]
-- generateFU C 0 = []
-- generateFU C n = [Cycle $ genericReplicate n ()]
-- generateFU (OfSize f p) n | p n = generateFU f n
--                           | otherwise = []
-- generateFU (OfSizeExactly f s) n | s == n = generateFU f n
--                                  | otherwise = []
-- generateFU (f :><: g) n = [ Prod (x,y) | x <- generateFU f n
--                                        , y <- generateFU g n
--                           ]

-- expandPartition :: [(Integer, Integer)] -> [Integer]
-- expandPartition = concatMap (uncurry (flip genericReplicate))

