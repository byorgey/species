{-# LANGUAGE NoImplicitPrelude
           , CPP
           , GADTs
           , FlexibleContexts
           , ScopedTypeVariables
           , KindSignatures
           , TypeFamilies
           , DeriveDataTypeable
           , TypeOperators
  #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Math.Combinatorics.Species.Enumerate
-- Copyright   :  (c) Brent Yorgey 2010
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@cis.upenn.edu
-- Stability   :  experimental
--
-- Enumeration (i.e. exhaustive generation of structures) of both
-- labeled and unlabeled species.
--
-----------------------------------------------------------------------------

module Math.Combinatorics.Species.Enumerate
    (
      -- * Enumeration methods

      enumerate

    , enumerateL
    , enumerateU
    , enumerateM

    , enumerateAll
    , enumerateAllU

    -- * Tools for dealing with structure types

    , Enumerable(..)

    , Structure(..), extractStructure, unsafeExtractStructure
    , structureType, showStructureType

    -- * Where all the work actually happens

    , enumerate', enumerateE

    ) where

import Math.Combinatorics.Species.Class
import Math.Combinatorics.Species.Types
import Math.Combinatorics.Species.AST
import Math.Combinatorics.Species.Structures
import qualified Math.Combinatorics.Species.Util.Interval as I

import qualified Math.Combinatorics.Multiset as MS
import Math.Combinatorics.Multiset (Multiset(..), (+:))

import Data.Typeable

import NumericPrelude
#if MIN_VERSION_numeric_prelude(0,2,0)
#else
import PreludeBase hiding (cycle)
#endif

-- | Given an AST describing a species, with a phantom type parameter
--   representing the structure of the species, and an underlying
--   multiset of elements, compute a list of all possible structures
--   built over the underlying multiset.  (Of course, it would be
--   really nice to have a real dependently-typed language for this!)
--
--   Unfortunately, 'TSpeciesAST' cannot be made an instance of
--   'Species', so if we want to be able to enumerate structures given
--   an expression of the 'Species' DSL as input, the output must be
--   existentially quantified; see 'enumerateE'.
--
--   Generating structures over base elements from a /multiset/
--   unifies labeled and unlabeled generation into one framework.
--   To enumerate labeled structures, use a multiset where each
--   element occurs exactly once; to enumerate unlabeled structures,
--   use a multiset with the desired number of copies of a single
--   element.  To do labeled generation we could get away without the
--   generality of multisets, but to do unlabeled generation we need
--   the full generality anyway.
--
--   'enumerate'' does all the actual work, but is not meant to be used
--   directly; use one of the specialized @enumerateXX@ methods.
enumerate' :: TSpeciesAST s -> Multiset a -> [s a]
enumerate' TZero _               = []
enumerate' TOne (MS [])          = [Unit]
enumerate' TOne _                = []
enumerate' (TN n) (MS [])        = map Const [1..n]
enumerate' (TN _) _              = []
enumerate' TX (MS [(x,1)])       = [Id x]
enumerate' TX _                  = []
enumerate' TE xs                 = [Set (MS.toList xs)]
enumerate' TC m                  = map Cycle (MS.cycles m)
enumerate' TL xs                 = MS.permutations xs
enumerate' TSubset xs            = map (Set . MS.toList . fst) (MS.splits xs)
enumerate' (TKSubset k) xs       = map (Set . MS.toList)
                                      (MS.kSubsets (fromIntegral k) xs)
enumerate' TElt xs               = map (Id . fst) . MS.toCounts $ xs
enumerate' (f :+:: g) xs         = map Inl (enumerate' (stripI f) xs)
                                ++ map Inr (enumerate' (stripI g) xs)

  -- A better solution here might be to change MS.splits to only
  -- return splits which are of appropriate sizes.

enumerate' (f :*:: g) xs         = [ x :*: y
                                   | (s1,s2) <- MS.splits xs
                                   ,            (fromIntegral $ MS.size s1) `I.elem` (getI f)
                                   ,            (fromIntegral $ MS.size s2) `I.elem` (getI g)
                                   ,       x <- enumerate' (stripI f) s1
                                   ,       y <- enumerate' (stripI g) s2
                                   ]
enumerate' (f :.:: g) xs         = [ Comp y
                                   | p   <- MS.partitions xs
                                   ,        (fromIntegral $ MS.size p) `I.elem` (getI f)
                                   ,        all ((`I.elem` (getI g)) . fromIntegral . MS.size) (MS.toList p)
                                   , xs' <- MS.sequenceMS . fmap (enumerate' (stripI g)) $ p
                                   , y   <- enumerate' (stripI f) xs'
                                   ]
enumerate' (f :><:: g) xs
  | any (/= 1) $ MS.getCounts xs
  = error "Unlabeled enumeration does not (yet) work with cartesian product."
enumerate' (f :><:: g) xs        = [ x :*: y
                                   | x <- enumerate' (stripI f) xs
                                   , y <- enumerate' (stripI g) xs
                                   ]

enumerate' (f :@:: g) xs
  | any (/= 1) $ MS.getCounts xs
  = error "Unlabeled enumeration does not (yet) work with functor composition."
enumerate' (f :@:: g) xs         = map Comp
                                   . enumerate' (stripI f)
                                   . MS.fromDistinctList
                                   . enumerate' (stripI g)
                                   $ xs
enumerate' (TDer f) xs           = map Comp
                                   . enumerate' (stripI f)
                                   $ (Star,1) +: fmap Original xs
enumerate' (TNonEmpty f) (MS []) = []
enumerate' (TNonEmpty f) xs      = enumerate' (stripI f) xs
enumerate' (TRec f) xs           = map Mu $ enumerate' (apply f (TRec f)) xs
enumerate' (TOfSize f p) xs
  | p (fromIntegral . sum . MS.getCounts $ xs)
    = enumerate' (stripI f) xs
  | otherwise = []
enumerate' (TOfSizeExactly f n) xs
  | (fromIntegral . sum . MS.getCounts $ xs) == n
    = enumerate' (stripI f) xs
  | otherwise = []

-- | An existential wrapper for structures, hiding the structure
--   functor and ensuring that it is 'Typeable'.
data Structure a where
  Structure :: Typeable f => f a -> Structure a

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
-- > enumerate s ls :: [T a]
--
--   where @ls :: [a]@.
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
--
-- Note, however, that providing a type annotation on 'enumerate' in
-- this way is usually only necessary at the @ghci@ prompt; when used
-- in the context of a larger program the type of a call to
-- 'enumerate' can often be inferred.
structureType :: ESpeciesAST -> String
structureType (Wrap s) = showStructureType . extractType $ (stripI s)
  where extractType :: forall s. Typeable s => TSpeciesAST s -> TypeRep
        extractType _ = typeOf1 (undefined :: s ())

-- | Show a 'TypeRep' while stripping off qualifier portions of 'TyCon'
--   names.  This is essentially copied and pasted from the
--   "Data.Typeable" source, with a number of cases taken out that we
--   don't care about (special cases for @(->)@, tuples, etc.).
showStructureType :: TypeRep -> String
showStructureType t = showsPrecST 0 t ""
  where showsPrecST :: Int -> TypeRep -> ShowS
        showsPrecST p t =
          case splitTyConApp t of
            (tycon, [])   -> showString (dropQuals $ tyConName tycon)
            (tycon, [x])  | tyConName tycon == "[]"
                              -> showChar '[' . showsPrecST 11 x . showChar ']'
            (tycon, args) -> showParen (p > 9)
                               $ showString (dropQuals $ tyConName tycon)
                               . showChar ' '
                               . showArgsST args

        showArgsST :: [TypeRep] -> ShowS
        showArgsST []     = id
        showArgsST [t]    = showsPrecST 10 t
        showArgsST (t:ts) = showsPrecST 10 t . showChar ' ' . showArgsST ts

        dropQuals :: String -> String
        dropQuals = reverse . takeWhile (/= '.') . reverse

-- | 'enumerateE' is a variant of 'enumerate'' which takes an
--   (existentially quantified) typed AST and returns a list of
--   existentially quantified structures.  This is also not meant to
--   be used directly.  Instead, you should use one of the other
--   @enumerateX@ methods.
enumerateE :: ESpeciesAST -> Multiset a -> [Structure a]
enumerateE (Wrap s) m
  | fromIntegral (sum (MS.getCounts m)) `I.elem` (getI s)
    = map Structure (enumerate' (stripI s) m)
  | otherwise = []

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
--   enumerating the structures of a particular species at the @ghci@
--   prompt, see the 'structureType' function.  To be able to use your
--   own custom data type in an enumeration, just make your data type
--   an instance of the 'Enumerable' type class; this can be done for
--   you automatically by "Math.Combinatorics.Species.TH".
--
--   If an invalid type annotation is given, 'enumerate' will call
--   'error' with a helpful error message.  This should not be much of
--   an issue in practice, since usually 'enumerate' will be used at a
--   specific type; it's hard to imagine a usage of 'enumerate' which
--   will sometimes work and sometimes fail.  However, those who like
--   their functions total can use 'extractStructure' to make a
--   version of 'enumerate' (or the other variants) with a return type
--   of @['Either' 'String' (f a)]@ (which will return an annoying ton of
--   duplicate error messages) or @'Either' 'String' [f a]@ (which has the
--   unfortunate property of being much less lazy than the current
--   versions, since it must compute the entire list before deciding
--   whether to return @'Left'@ or @'Right'@).
--
--   For slight variants on 'enumerate', see 'enumerateL',
--   'enumerateU', and 'enumerateM'.
enumerate :: (Enumerable f, Typeable a, Eq a) => SpeciesAST -> [a] -> [f a]
enumerate s = enumerateM s . MS.fromListEq

-- | Labeled enumeration: given a species expression and a list of
--   labels (which are assumed to be distinct), compute the list of
--   all structures built from the given labels.  If the type given
--   for the enumeration does not match the species expression (via an
--   'Enumerable' instance), call 'error' with an error message
--   explaining the mismatch.  This is slightly more efficient than
--   'enumerate' for lists of labels which are known to be distinct,
--   since it doesn't have to waste time checking for
--   duplicates. (However, it probably doesn't really make much
--   difference, since the time to do the actual enumeration will
--   usually dwarf the time to process the list of labels anyway.)
--
--   For example:
--
--   > > enumerateL ballots [1,2,3] :: [Comp [] Set Int]
--   > [[{1,2,3}],[{2,3},{1}],[{1},{2,3}],[{2},{1,3}],[{1,3},{2}],[{3},{1,2}]
--   > ,[{1,2},{3}],[{3},{2},{1}],[{3},{1},{2}],[{2},{3},{1}],[{2},{1},{3}]
--   > ,[{1},{3},{2}],[{1},{2},{3}]]
enumerateL :: (Enumerable f, Typeable a) =>  SpeciesAST -> [a] -> [f a]
enumerateL s = enumerateM s . MS.fromDistinctList

-- | Unlabeled enumeration: given a species expression and an integer
--   indicating the number of labels to use, compute the list of all
--   unlabeled structures of the given size.  If the type given for
--   the enumeration does not match the species expression, call
--   'error' with an error message explaining the mismatch.
--
--   Note that @'enumerateU' s n@ is equivalent to @'enumerate' s
--   (replicate n ())@.
--
--   For example:
--
--   > > enumerateU octopi 4 :: [Comp Cycle [] ()]
--   > [<[(),(),(),()]>,<[(),()],[(),()]>,<[(),(),()],[()]>
--   > ,<[(),()],[()],[()]>,<[()],[()],[()],[()]>]
enumerateU ::  Enumerable f => SpeciesAST -> Int -> [f ()]
enumerateU s n = enumerateM s (MS.fromCounts [((),n)])

-- | General enumeration: given a species expression and a multiset of
--   labels, compute the list of all distinct structures built from
--   the given labels. If the type given for the enumeration does not
--   match the species expression, call 'error' with a message
--   explaining the mismatch.
enumerateM :: (Enumerable f, Typeable a) => SpeciesAST -> Multiset a -> [f a]
enumerateM s m = map unsafeExtractStructure $ enumerateE (annotate s) m

-- | Lazily enumerate all unlabeled structures.
--
--   For example:
--
--   > > take 10 $ enumerateAllU octopi :: [Comp Cycle [] ()]
--   > [<[()]>,<[(),()]>,<[()],[()]>,<[(),(),()]>,<[(),()],[()]>
--   > ,<[()],[()],[()]>,<[(),(),(),()]>,<[(),()],[(),()]>
--   > ,<[(),(),()],[()]>,<[(),()],[()],[()]>]
enumerateAllU :: Enumerable f => SpeciesAST -> [f ()]
enumerateAllU s = concatMap (enumerateU s) [0..]

-- | Lazily enumerate all labeled structures, using [1..] as the
--   labels.
--
--   For example:
--
--   > > take 10 $ enumerateAll ballots :: [Comp [] Set Int]
--   > [[],[{1}],[{1,2}],[{2},{1}],[{1},{2}],[{1,2,3}],[{2,3},{1}]
--   > ,[{1},{2,3}],[{2},{1,3}],[{1,3},{2}]]
enumerateAll :: Enumerable f => SpeciesAST -> [f Int]
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
--   You should only rarely have to explicitly make an instance of
--   'Enumerable' yourself; Template Haskell code to derive instances
--   for you is provided in "Math.Combinatorics.Species.TH".
class Typeable (StructTy f) => Enumerable (f :: * -> *) where
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

instance (Enumerable f, Enumerable g) => Enumerable (f :+: g) where
  type StructTy (f :+: g) = StructTy f :+: StructTy g
  iso (Inl x) = Inl (iso x)
  iso (Inr y) = Inr (iso y)

instance (Enumerable f, Enumerable g) => Enumerable (f :*: g) where
  type StructTy (f :*: g) = StructTy f :*: StructTy g
  iso (x :*: y) = iso x :*: iso y

instance (Enumerable f, Functor f, Enumerable g) => Enumerable (f :.: g) where
  type StructTy (f :.: g) = StructTy f :.: StructTy g
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

instance Enumerable Maybe where
  type StructTy Maybe = Unit :+: Id
  iso (Inl Unit)   = Nothing
  iso (Inr (Id x)) = Just x
