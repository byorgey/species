{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import Data.List (genericReplicate, nub, sort)
import Control.Arrow (first, second)
import Data.Maybe (catMaybes)

import Test.QuickCheck

type Occur = Int

-- | A multiset is a list of (element, count) pairs.  We maintain the
--   invariants that the counts are always positive, and no element
--   ever appears more than once.
type MultiSet a n = [(a, n)]

-- | Convert a multiset to a list.
toList :: Integral n => MultiSet a n -> [a]
toList = concatMap (uncurry (flip genericReplicate))

-- | In order to generate permutations of a multiset, we need to keep
--   track of the most recently used element in the permutation being
--   built, so that we don't use it again immediately.  The
--   'MSWithAvoid' type records this information, consisting of a
--   multiset possibly paired with an element (with multiplicity)
--   which is also part of the multiset, but should not be used at the
--   beginning of permutations.
data MSWithAvoid a n = MSA (Maybe (a, n)) (MultiSet a n)
  deriving Show

-- | Convert a 'MultiSet' to a 'MSWithAvoid' (with no avoided element).
toMSA :: MultiSet a n -> MSWithAvoid a n
toMSA = MSA Nothing

-- | Convert a 'MSWithAvoid' to a 'MultiSet'.
fromMSA :: MSWithAvoid a n -> MultiSet a n
fromMSA (MSA Nothing m)  = m
fromMSA (MSA (Just e) m) = e:m

-- | List all the _distinct_ permutations of the elements of a
--   multiset.
permutations :: Integral n => MultiSet a n -> [[a]]
permutations [] = [[]]
permutations m  = permutations' (toMSA m)

-- | List all the distinct permutations of the elements of a multiset
--   which do not start with the element to avoid (if any).
permutations' :: Integral n => MSWithAvoid a n -> [[a]]

-- If only one element is left, there's only one permutation.
permutations' (MSA Nothing [(x,n)]) = [genericReplicate n x]

-- Otherwise, select an element+multiplicity in all possible ways, and
-- concatenate the elements to all possible permutations of the
-- remaining multiset.
permutations' m  = [ genericReplicate k x ++ p
                     | ((x,k), m') <- selectMSA m
                     , p           <- permutations' m'
                   ]

-- | Select an element + multiplicity from a multiset in all possible
--   ways, appropriately keeping track of elements to avoid at the
--   start of permutations.
selectMSA :: Integral n => MSWithAvoid a n -> [((a, n), MSWithAvoid a n)]

-- No elements to select.
selectMSA (MSA _ [])            = []

-- Selecting from a multiset with n copies of x, avoiding e:
selectMSA (MSA e ((x,n) : ms))  =

  -- If we select all n copies of x, there are no copies of x left to avoid;
  -- stick e (if it exists) back into the remaining multiset.
  ((x,n), MSA Nothing (maybe ms (:ms) e)) :

  -- We can also select any number of copies of x from (n-1) down to 1; in each case,
  -- we avoid the remaining copies of x and put e back into the returned multiset.
  [ ( (x,k), MSA (Just (x,n-k))
                 (maybe ms (:ms) e) )
    | k <- [n-1, n-2 .. 1]
  ] ++

  -- Finally, we can recursively choose something other than x.
  map (second (consMSA (x,n))) (selectMSA (MSA e ms))

consMSA :: (a, n) -> MSWithAvoid a n -> MSWithAvoid a n
consMSA x (MSA e m) = MSA e (x:m)


-- Some QuickCheck properties.  Of course, due to combinatorial
-- explosion these are of limited utility!
newtype Count = Count Int
  deriving (Eq, Show, Num, Real, Enum, Ord, Integral)

instance Arbitrary Count where
  arbitrary = elements (map Count [1..3])

prop_perms_distinct :: MultiSet Char Count -> Bool
prop_perms_distinct m = length ps == length (nub ps)
  where ps = permutations m

prop_perms_are_perms :: MultiSet Char Count -> Bool
prop_perms_are_perms m = all ((==l') . sort) (permutations m)
  where l' = sort (toList m)

---------------------
-- Partitions
---------------------

-- | Element count vector.
type Counts n = [n]

-- | Componentwise comparison of count vectors.
(<|=) :: Ord n => Counts n -> Counts n -> Bool
xs <|= ys = and $ zipWith (<=) xs ys

-- | 'vUnit v' produces a unit vector of the same length as @v@.
vUnit :: Num n => Counts n -> Counts n
vUnit []     = []
vUnit [_]    = [1]
vUnit (_:xs) = 0 : vUnit xs

-- | 'vZero v' produces a zero vector of the same length as @v@.
vZero :: Num n => Counts n -> Counts n
vZero = map (const 0)

-- | Test for the zero vector.
vIsZero :: Num n => Counts n -> Bool
vIsZero = all (==0)

-- | Do vector arithmetic componentwise.
(.+.), (.-.) :: Num n => Counts n -> Counts n -> Counts n
(.+.) = zipWith (+)
(.-.) = zipWith (-)

-- | Multiply a count vector by a scalar.
(*.) :: Num n => n -> Counts n -> Counts n
(*.) n = map (n*)

vDiv :: Integral n => Counts n -> Counts n -> n
vDiv v1 v2 = minimum . catMaybes $ zipWith zdiv v1 v2
  where zdiv _ 0 = Nothing
        zdiv x y = Just $ x `div` y

vInc :: (Num n, Ord n) => Counts n -> Counts n -> Counts n
vInc lim v = reverse (vInc' (reverse lim) (reverse v))
  where vInc' _ []          = []
        vInc' [] (x:xs)     = x+1 : xs
        vInc' (l:ls) (x:xs) | x < l     = x+1 : xs
                            | otherwise = 0 : vInc' ls xs

vPartitions :: Integral n => Counts n -> [MultiSet (Counts n) n]
vPartitions v = vPart v (vZero v) where
  vPart v _ | vIsZero v = [[]]
  vPart v vL
    | v <= vL   = []
    | otherwise = [(v,1)] : [ (v',k) : p' | v' <- withinFromTo v (vHalf v) (vInc v vL)
                                          , k  <- [1 .. (v `vDiv` v')]
                                          , p' <- vPart (v .-. (k *. v')) v' ]

vHalf :: Integral n => Counts n -> Counts n
vHalf [] = []
vHalf (x:xs) | (even x) = (x `div` 2) : vHalf xs
             | otherwise = (x `div` 2) : xs

downFrom :: (Num n, Enum n) => n -> [n]
downFrom n = [n,(n-1)..0]

-- | 'within m' generates a decreasing list of vectors 'v <|= m'.
within :: (Num n, Enum n) => Counts n -> [Counts n]
within = sequence . map downFrom

clip :: Ord n => Counts n -> Counts n -> Counts n
clip = zipWith min

withinFromTo :: (Num n, Enum n, Ord n) =>
                Counts n -> Counts n -> Counts n -> [Counts n]
withinFromTo m s e | not (s <|= m) = withinFromTo m (clip m s) e
withinFromTo m s e | e > s = []
withinFromTo m s e = wFT m s e True True
  where
    wFT [] _ _ _ _ = [[]]
    wFT (m:ms) (s:ss) (e:es) useS useE =
        let start = if useS then s else m
            end   = if useE then e else 0
        in
          [x:xs | x <- [start,(start-1)..end],
                  let useS' = useS && x==s,
                  let useE' = useE && x==e,
                  xs <- wFT ms ss es useS' useE' ]

partitions :: Integral n => MultiSet a n -> [MultiSet (MultiSet a n) n]
partitions [] = [[]]
partitions m  = (map . map . first) (combine elts) $ vPartitions counts
  where (elts, counts) = unzip m
        combine es cs  = filter ((/=0) . snd) $ zip es cs