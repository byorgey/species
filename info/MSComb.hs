{--------------------------------------------------------------------
  Combinatorics
--------------------------------------------------------------------}

-- | XXX. List all the _distinct_ permutations of the elements of a
--   multiset.
permutations :: MultiSet a -> [[a]]
permutations m
  | null m    = [[]]
  | otherwise = [ replicate k y ++ p
                  | ((y,k), m') <- select m
                  , p           <- permutations m'
                ]
 where select m = [ ((y,k), m')
                    | (y,n) <- toOccurList m
                    , k     <- [n, n-1 .. 1]
                    , let m' = deleteMany y
                            deleteMany :: Ord a => a -> Occur -> MultiSet a -> MultiSet a
