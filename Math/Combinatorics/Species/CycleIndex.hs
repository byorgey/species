module Math.Combinatorics.Species.CycleIndex where

import Math.Combinatorics.Species.Class

import qualified MathObj.MultiVarPolynomial as MVP
import qualified MathObj.Monomial as Monomial
import qualified MathObj.FactoredRational as FQ

instance Species (MVP.T Rational) where
  singleton = MVP.x 1
  set       = MVP.Cons . map partToMonomial . concatMap intPartitions $ [0..]

  cycle     = MVP.Cons . concatMap cycleMonomials $ [1..]

  o         = MVP.compose
  nonEmpty  p@(MVP.Cons (x:xs)) | Monomial.degree x == 0 = MVP.Cons xs
                                | otherwise              = p

  (MVP.Cons (x:_)) .: (MVP.Cons (y:ys)) = MVP.Cons (x:rest)
    where rest | Monomial.pDegree y == 0 = ys
               | otherwise               = (y:ys)

partToMonomial :: [(Integer, Integer)] -> Monomial.T Rational
partToMonomial js = Monomial.Cons (zCoeff js) (M.fromList js)

zCoeff :: [(Integer, Integer)] -> Rational
zCoeff js = toRational $ 1 / aut js

aut :: [(Integer, Integer)] -> FQ.T
aut = product . map (\(b,e) -> FQ.factorial e * (fromInteger b)^e)

intPartitions :: Integer -> [[(Integer, Integer)]]
intPartitions n = intPartitions' n n
  where intPartitions' :: Integer -> Integer -> [[(Integer,Integer)]]
        intPartitions' 0 _ = [[]]
        intPartitions' n 0 = []
        intPartitions' n k =
          [ if (j == 0) then js else (k,j):js
            | j <- reverse [0..n `div` k]
            , js <- intPartitions' (n - j*k) (min (k-1) (n - j*k)) ]

cycleMonomials :: Integer -> [Monomial.T Rational]
cycleMonomials n = map cycleMonomial ds
  where n' = fromIntegral n
        ds = sort . FQ.divisors $ n'
        cycleMonomial d = Monomial.Cons (FQ.eulerPhi (n' / d) % n)
                                        (M.singleton (n `div` (toInteger d)) (toInteger d))

zToLabelled :: MVP.T Rational -> Labelled
zToLabelled (MVP.Cons xs) 
  = Labelled . PowerSeries.fromCoeffs . map LR
  . insertZeros
  . concatMap (\(c,as) -> case as of { [] -> [(0,c)] ; [(1,p)] -> [(p,c)] ; _ -> [] })
  . map (Monomial.coeff &&& (M.assocs . Monomial.powers))
  $ xs

zToUnlabelled :: MVP.T Rational -> Unlabelled
zToUnlabelled (MVP.Cons xs)
  = Unlabelled . PowerSeries.fromCoeffs . map numerator
  . insertZeros
  . map ((fst . head) &&& (sum . map snd))
  . groupBy ((==) `on` fst)
  . map ((sum . map (uncurry (*)) . M.assocs . Monomial.powers) &&& Monomial.coeff)
  $ xs

insertZeros :: Ring.C a => [(Integer, a)] -> [a]
insertZeros = insertZeros' [0..]
  where
    insertZeros' _ [] = repeat 0
    insertZeros' (n:ns) ((pow,c):pcs) 
      | n < pow   = genericReplicate (pow - n) 0 
                    ++ insertZeros' (genericDrop (pow - n) (n:ns)) ((pow,c):pcs)
      | otherwise = c : insertZeros' ns pcs
