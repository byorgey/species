{-# LANGUAGE NoImplicitPrelude
           , GADTs
           , FlexibleContexts
           , ScopedTypeVariables
           , KindSignatures
           , TypeFamilies
           , DeriveDataTypeable
  #-}

-- | Enumeration of labelled and unlabelled species.
module Math.Combinatorics.Species.Enumerate
    (
      -- * Enumeration methods

      enumerate

    , enumerateL
    , enumerateU
    , enumerateM

    , enumerateAll
    , enumerateAllU

    -- * Where all the work actually happens

    , enumerate', enumerateE

    -- * Tools for dealing with structure types

    , Enumerable(..)

    , Structure(..), extractStructure, unsafeExtractStructure
    , structureType, showStructureType

    ) where

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Types
import Math.Combinatorics.Species.AST
import Math.Combinatorics.Species.Structures

import qualified Math.Combinatorics.Multiset as MS
import Math.Combinatorics.Multiset (Multiset(..), (+:))

import Data.Typeable

import NumericPrelude
import PreludeBase hiding (cycle)

-- | Given an AST describing a species, with a phantom type parameter
--   representing the structure of the species, and an underlying
--   multiset of elements, compute a list of all possible structures
--   built over the underlying multiset.  (Of course, it would be
--   really nice to have a real dependently-typed language for this!)
--
--   Unfortunately, 'SpeciesAST' cannot be made an instance of
--   'Species', so if we want to be able to enumerate structures given
--   an expression of the 'Species' DSL as input, we must take
--   'ESpeciesAST' as input, which existentially wraps the phantom
--   structure type---but this means that the output list type must be
--   existentially quantified as well; see 'enumerateE'.
--
--   Generating structures over base elements from a /multiset/
--   unifies labelled and unlabelled generation into one framework.
--   To enumerate labelled structures, use a multiset where each
--   element occurs exactly once; to enumerate unlabelled structures,
--   use a multiset with the desired number of copies of a single
--   element.  To do labelled generation we could get away without the
--   generality of multisets, but to do unlabelled generation we need
--   the full generality anyway.
--
--   'enumerate'' does all the actual work, but is not meant to be used
--   directly; use one of the specialized @enumerateXX@ methods.
enumerate' :: SpeciesAST s -> Multiset a -> [s a]
enumerate' Zero _               = []
enumerate' One (MS [])          = [Unit]
enumerate' One _                = []
enumerate' (N n) (MS [])        = map Const [1..n]
enumerate' (N _) _              = []
enumerate' X (MS [(x,1)])       = [Id x]
enumerate' X _                  = []
enumerate' E xs                 = [Set (MS.toList xs)]
enumerate' C m                  = map Cycle (MS.cycles m)
enumerate' L xs                 = MS.permutations xs
enumerate' Subset xs            = map (Set . MS.toList . fst) (MS.splits xs)
enumerate' (KSubset k) xs       = map (Set . MS.toList)
                                      (MS.kSubsets (fromIntegral k) xs)
enumerate' Elt xs               = map (Id . fst) . MS.toCounts $ xs
enumerate' (f :+: g) xs         = map Inl (enumerate' f xs)
                               ++ map Inr (enumerate' g xs)
enumerate' (f :*: g) xs         = [ Prod x y
                                  | (s1,s2) <- MS.splits xs
                                  ,       x <- enumerate' f s1
                                  ,       y <- enumerate' g s2
                                  ]
enumerate' (f :.: g) xs         = [ Comp y
                                  | p   <- MS.partitions xs
                                  , xs' <- MS.sequenceMS . fmap (enumerate' g) $ p
                                  , y   <- enumerate' f xs'
                                  ]
enumerate' (f :><: g) xs        = [ Prod x y
                                  | x <- enumerate' f xs
                                  , y <- enumerate' g xs
                                  ]
enumerate' (f :@: g) xs         = map Comp
                                  . enumerate' f
                                  . MS.fromDistinctList
                                  . enumerate' g
                                  $ xs
enumerate' (Der f) xs           = map Comp
                                  . enumerate' f
                                  $ (Star,1) +: fmap Original xs
enumerate' (NonEmpty f) (MS []) = []
enumerate' (NonEmpty f) xs      = enumerate' f xs
enumerate' (Rec f) xs           = map Mu $ enumerate' (apply f (Rec f)) xs
enumerate' (OfSize f p) xs
  | p (fromIntegral . sum . MS.getCounts $ xs)
    = enumerate' f xs
  | otherwise = []
enumerate' (OfSizeExactly f n) xs
  | (fromIntegral . sum . MS.getCounts $ xs) == n
    = enumerate' f xs
  | otherwise = []

-- | An existential wrapper for structures, hiding the structure
--   functor and ensuring that it is 'Typeable'.
data Structure a where
  Structure :: Typeable1 f => f a -> Structure a

-- | Extract the contents from a 'Structure' wrapper, if we know the
--   type, and map it into an isomorphic type.  If the type doesn't
--   match, return a helpful error message instead.
extractStructure :: forall f a. (Enumerable f, Typeable a) =>
                      Structure a -> Either String (f a)
extractStructure (Structure s) =
  case cast s of
    Nothing -> Left $
          "Structure type mismatch.\n"
       ++ "  Expected: " ++ showStructureType (typeOf (undefined :: StructTy f a)) ++ "\n"
       ++ "  Inferred: " ++ showStructureType (typeOf s)
    Just y -> Right (iso y)

-- | A version of 'extractStructure' which calls 'error' with the
--   message in the case of a type mismatch, instead of returning an
--   'Either'.
unsafeExtractStructure :: (Enumerable f, Typeable a) => Structure a -> f a
unsafeExtractStructure = either error id . extractStructure

-- | @'structureType' s@ returns a String representation of the
--   functor type which represents the structure of the species @s@.
--   In particular, if @structureType s@ prints @\"T\"@, then you can
--   safely use 'enumerate' and friends by writing
--
-- > enumerate s ls :: [T L]
--
--   where @ls :: [L]@.
--
--   For example,
--
-- > > structureType octopus
-- > "Comp Cycle []"
-- > > enumerate octopus [1,2,3] :: [Comp Cycle [] Int]
-- > [<[3,2,1]>,<[3,1,2]>,<[2,3,1]>,<[2,1,3]>,<[1,3,2]>
-- > ,<[1,2,3]>,<[1],[3,2]>,<[1],[2,3]>,<[3,1],[2]>
-- > ,<[1,3],[2]>,<[2,1],[3]>,<[1,2],[3]>,<[2],[1],[3]>
-- > ,<[1],[2],[3]>]
structureType :: ESpeciesAST -> String
structureType (SA s) = showStructureType . extractType $ s
  where extractType :: forall s. Typeable1 s => SpeciesAST s -> TypeRep
        extractType _ = typeOf1 (undefined :: s ())

-- | Show a 'TypeRep' while stripping off qualifier portions of 'TyCon'
--   names.  This is essentially copied and pasted from the
--   "Data.Typeable source", with a number of cases taken out that we
--   don't care about (special cases for @(->)@, tuples, etc.).
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

-- | 'enumerateE' is a variant of 'enumerate'' which takes an
--   (existentially quantified) 'ESpeciesAST' and returns a list of
--   structures wrapped in the (also existentially quantified)
--   'Structure' type.  This is also not meant to be used directly.
--   Instead, you should use one of the other @enumerateX@ methods.
enumerateE :: ESpeciesAST -> Multiset a -> [Structure a]
enumerateE (SA s) m = map Structure (enumerate' s m)

-- XXX add examples to all of these.

-- | @enumerate s ls@ computes a complete list of distinct
--   @s@-structures over the underlying multiset of labels @ls@.  For
--   example:
--
-- > > enumerate octopi [1,2,3] :: [Comp Cycle [] Int]
-- > [<[3,2,1]>,<[3,1,2]>,<[2,3,1]>,<[2,1,3]>,<[1,3,2]>,<[1,2,3]>,
-- >  <[1],[3,2]>,<[1],[2,3]>,<[3,1],[2]>,<[1,3],[2]>,<[2,1],[3]>,
-- >  <[1,2],[3]>,<[2],[1],[3]>,<[1],[2],[3]>]
-- >
-- > > enumerate octopi [1,1,2] :: [Comp Cycle [] Int]
-- > [<[2,1,1]>,<[1,2,1]>,<[1,1,2]>,<[2,1],[1]>,<[1,2],[1]>,
-- >  <[1,1],[2]>,<[1],[1],[2]>]
-- >
-- > > enumerate subsets "abc" :: [Set Int]
-- > [{'a','b','c'},{'a','b'},{'a','c'},{'a'},{'b','c'},{'b'},{'c'},{}]
-- >
-- > > enumerate simpleGraphs [1,2,3] :: [Comp Set Set Int]
-- > [{{1,2},{1,3},{2,3}},{{1,2},{1,3}},{{1,2},{2,3}},{{1,2}},{{1,3},{2,3}},
-- >  {{1,3}},{{2,3}},{}]
--
--   There is one caveat: since the type of the generated structures
--   is different for each species, they must be cast (using the magic
--   of "Data.Typeable") out of an existential wrapper; this is why
--   type annotations are required in all the examples above.  Of
--   course, if a call to 'enumerate' is used in the context of some
--   larger program, a type annotation will probably not be needed,
--   due to the magic of type inference.
--
--   For help in knowing what type annotation you can give when
--   enumerating the structures of a particular species, see the
--   'structureType' function.  To be able to use your own custom data
--   type in an enumeration, just make your data type an instance of
--   the 'Enumerable' type class.
--
--   If an invalid type annotation is given, 'enumerate' will call
--   'error' with a helpful error message.  This should not be much of
--   an issue in practice, since usually 'enumerate' will be used at a
--   specific type; it's hard to imagine a usage of 'enumerate' which
--   will sometimes work and sometimes fail.  However, those who like
--   their functions total can use 'extractStructure' to make a
--   version of 'enumerate' (or the other variants) with a return type
--   of @[Either String (f a)]@ (which will return an annoying ton of
--   duplicate error message) or @Either String [f a]@ (which has the
--   unfortunate property of being much less lazy than the current
--   versions, since it must compute the entire list before deciding
--   whether to return @Left@ or @Right@).
--
--   For slight variants on 'enumerate', see 'enumerateL',
--   'enumerateU', and 'enumerateM'.
enumerate :: (Enumerable f, Typeable a, Eq a) => ESpeciesAST -> [a] -> [f a]
enumerate s = enumerateM s . MS.fromListEq

-- | Labelled enumeration: given a species expression and a list of
--   labels (which are assumed to be distinct), compute the list of
--   all structures built from the given labels.  If the type given
--   for the enumeration does not match the species expression (via an
--   'Enumerable' instance), call 'error' with an error message
--   explaining the mismatch.
enumerateL :: (Enumerable f, Typeable a) =>  ESpeciesAST -> [a] -> [f a]
enumerateL s = enumerateM s . MS.fromDistinctList

-- | Unlabelled enumeration: given a species expression and an integer
--   indicating the number of labels to use, compute the list of all
--   unlabelled structures of the given size.  If the type given for
--   the enumeration does not match the species expression, call
--   'error' with an error message explaining the mismatch.
--
--   Note that @'enumerateU' s n@ is equivalent to @'enumerate' s
--   (replicate n ())@.
enumerateU ::  Enumerable f => ESpeciesAST -> Int -> [f ()]
enumerateU s n = enumerateM s (MS.fromCounts [((),n)])

-- | General enumeration: given a species expression and a multiset of
--   labels, compute the list of all distinct structures built from
--   the given labels. If the type given for the enumeration does not
--   match the species expression, call 'error' with a message
--   explaining the mismatch.
enumerateM :: (Enumerable f, Typeable a) => ESpeciesAST -> Multiset a -> [f a]
enumerateM s m = map unsafeExtractStructure $ enumerateE s m

-- | Lazily enumerate all unlabelled structures.
enumerateAllU :: Enumerable f => ESpeciesAST -> [f ()]
enumerateAllU s = concatMap (enumerateU s) [0..]

-- | Lazily enumerate all labelled structures, using [1..] as the
--   labels.
enumerateAll :: Enumerable f => ESpeciesAST -> [f Int]
enumerateAll s = concatMap (\n -> enumerateL s (take n [1..])) [0..]

-- | The 'Enumerable' class allows you to enumerate structures of any
--   type, by declaring an instance of 'Enumerable'.  The 'Enumerable'
--   instance requires you to declare a standard structure type (see
--   "Math.Combinatorics.Species.Structures") associated with your
--   type, and a mapping 'iso' from the standard type to your custom
--   one.  Instances are provided for all the standard structure types
--   so you can enumerate species without having to provide your own
--   custom data type as the target of the enumeration if you don't
--   want to.
--
--   See "Math.Combinatorics.Species.Rec" for some example instances
--   of 'Enumerable'.
class Typeable1 (StructTy f) => Enumerable (f :: * -> *) where
  -- | The standard structure type (see
  --   "Math.Combinatorics.Species.Structures") that will map into @f@.
  type StructTy f :: * -> *

  -- | The mapping from @'StructTy' f@ to @f@.
  iso :: StructTy f a -> f a

instance Enumerable Void where
  type StructTy Void = Void
  iso = id

instance Enumerable Unit where
  type StructTy Unit = Unit
  iso = id

instance Typeable a => Enumerable (Const a) where
  type StructTy (Const a) = Const a
  iso = id

instance Enumerable Id where
  type StructTy Id = Id
  iso = id

instance (Enumerable f, Enumerable g) => Enumerable (Sum f g) where
  type StructTy (Sum f g) = Sum (StructTy f) (StructTy g)
  iso (Inl x) = Inl (iso x)
  iso (Inr y) = Inr (iso y)

instance (Enumerable f, Enumerable g) => Enumerable (Prod f g) where
  type StructTy (Prod f g) = Prod (StructTy f) (StructTy g)
  iso (Prod x y) = Prod (iso x) (iso y)

instance (Enumerable f, Functor f, Enumerable g) => Enumerable (Comp f g) where
  type StructTy (Comp f g) = Comp (StructTy f) (StructTy g)
  iso (Comp fgx) = Comp (fmap iso (iso fgx))

instance Enumerable [] where
  type StructTy [] = []
  iso = id

instance Enumerable Cycle where
  type StructTy Cycle = Cycle
  iso = id

instance Enumerable Set where
  type StructTy Set = Set
  iso = id

instance Enumerable Star where
  type StructTy Star = Star
  iso = id

instance Typeable f => Enumerable (Mu f) where
  type StructTy (Mu f) = Mu f
  iso = id