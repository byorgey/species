{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import Data.List (genericReplicate, nub, sort)
import Control.Arrow (second)

import Test.QuickCheck

type Occur = Int
type MultiSet a n = [(a, n)]

toList :: Integral n => MultiSet a n -> [a]
toList = concatMap (uncurry (flip genericReplicate))

data MSWithAvoid a n = MSA (Maybe (a, n)) (MultiSet a n)
  deriving Show

toMSA :: MultiSet a n -> MSWithAvoid a n
toMSA = MSA Nothing

fromMSA :: MSWithAvoid a n -> MultiSet a n
fromMSA (MSA Nothing m)  = m
fromMSA (MSA (Just e) m) = e:m

-- | List all the _distinct_ permutations of the elements of a
--   multiset.
permutations :: Integral n => MultiSet a n -> [[a]]
permutations [] = [[]]
permutations m  = permutations' (toMSA m)

permutations' :: Integral n => MSWithAvoid a n -> [[a]]
permutations' (MSA Nothing [(x,n)]) = [genericReplicate n x]
permutations' m  = [ genericReplicate k x ++ p
                     | ((x,k), m') <- selectMSA m
                     , p           <- permutations' m'
                   ]

selectMSA :: Integral n => MSWithAvoid a n -> [((a, n), MSWithAvoid a n)]
selectMSA (MSA _ [])            = []
selectMSA (MSA e ((x,n) : ms))  = ((x,n), MSA Nothing (maybe ms (:ms) e)) :
                                  [ ( (x,k), MSA (Just (x,n-k))
                                                 (maybe ms (:ms) e) )
                                    | k <- [n-1, n-2 .. 1]
                                  ] ++
                                  map (second (consMSA (x,n))) (selectMSA (MSA e ms))

consMSA :: (a, n) -> MSWithAvoid a n -> MSWithAvoid a n
consMSA x (MSA e m) = MSA e (x:m)

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
