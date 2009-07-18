{-# LANGUAGE NoImplicitPrelude 
           , GADTs
           , FlexibleInstances
           , GeneralizedNewtypeDeriving
  #-}

module Math.Combinatorics.Species where

import qualified MathObj.PowerSeries as PowerSeries
-- import qualified MathObj.EGF as EGF
import qualified MathObj.FactoredRational as FQ
import qualified MathObj.Monomial as Monomial
import qualified MathObj.MultiVarPolynomial as MVP

import qualified Algebra.Additive as Additive
import qualified Algebra.Ring as Ring
import qualified Algebra.Differential as Differential

import qualified Data.Map as M
import Control.Arrow ((&&&))
import Data.List (genericReplicate, genericDrop, groupBy, sort)
import Data.Function (on)

import NumericPrelude
import PreludeBase hiding (cycle)

unimplemented :: String -> a
unimplemented = error . (++ " is not yet implemented.")

--------------------------------------------------------------------------------
-- The class of species --------------------------------------------------------
--------------------------------------------------------------------------------

-- Differential requires s to be a differentiable ring.
class (Differential.C s) => Species s where
  singleton :: s             -- the species X of singletons
  set       :: s             -- the species E of sets
  cycle     :: s             -- the species C of cyclical orderings (cycles)
  o         :: s -> s -> s   -- partitional composition
  nonEmpty  :: s -> s

-- Some convenient synonyms and derived operations.
pointed, oneHole :: (Species s) => s -> s  
pointed = (singleton *) . Differential.differentiate
oneHole = Differential.differentiate

madeOf :: Species s => s -> s -> s
madeOf = o

x, singletons, e, sets, cycles :: Species s => s
x          = singleton
singletons = singleton
e          = set
sets       = set
cycles     = cycle

-- Some derived species.
list, lists :: Species s => s
list = oneHole cycle
lists = list

octopus, octopi :: Species s => s
octopus = cycle `o` nonEmpty lists
octopi = octopus

partition, partitions :: Species s => s
partition = set `o` nonEmpty sets
partitions = partition

--------------------------------------------------------------------------------
-- Unlabelled enumeration (classical power series) -----------------------------
--------------------------------------------------------------------------------

newtype Unlabelled = Unlabelled (PowerSeries.T Integer)
  deriving (Additive.C, Ring.C, Show)

instance Differential.C Unlabelled where
  differentiate = unimplemented "unlabelled differentiation"

instance Species Unlabelled where
  singleton = Unlabelled $ PowerSeries.fromCoeffs [0,1]
  set       = Unlabelled $ PowerSeries.fromCoeffs (repeat 1)
  cycle     = set
  o         = unimplemented "unlabelled composition"
  nonEmpty (Unlabelled (PowerSeries.Cons (_:xs))) = Unlabelled (PowerSeries.Cons (0:xs))
  nonEmpty x = x

unlabelled :: Unlabelled -> [Integer]
unlabelled (Unlabelled p) = PowerSeries.coeffs p

--------------------------------------------------------------------------------
-- Species algebra -------------------------------------------------------------
--------------------------------------------------------------------------------

data SpeciesAlg where
   N        :: Integer -> SpeciesAlg
   X        :: SpeciesAlg
   (:+:)    :: SpeciesAlg -> SpeciesAlg -> SpeciesAlg
   (:*:)    :: SpeciesAlg -> SpeciesAlg -> SpeciesAlg
   (:.:)    :: SpeciesAlg -> SpeciesAlg -> SpeciesAlg
   Der      :: SpeciesAlg -> SpeciesAlg
   E        :: SpeciesAlg
   C        :: SpeciesAlg
   NonEmpty :: SpeciesAlg -> SpeciesAlg
     deriving (Show)

instance Additive.C SpeciesAlg where
  zero   = N 0
  (+)    = (:+:)
  negate = error "negation is not implemented yet!  wait until virtual species..."

instance Ring.C SpeciesAlg where
  (*) = (:*:)
  one = N 1

instance Differential.C SpeciesAlg where
  differentiate = Der

instance Species SpeciesAlg where
  singleton = X
  set       = E
  cycle     = C
  o         = (:.:)
  nonEmpty  = NonEmpty

reify :: SpeciesAlg -> SpeciesAlg
reify = id

reflect :: Species s => SpeciesAlg -> s
reflect = undefined -- XXX

-- This is the basic idea: to do this right, we really want a more
--   sophisticated rewriting system.
simplify :: SpeciesAlg -> SpeciesAlg
simplify (N n :+: N m) = N (n+m)
simplify (N n :*: N m) = N (n*m)
simplify (N 0 :+: s)   = simplify s
simplify (s :+: N 0)   = simplify s
simplify (N 0 :*: s)   = N 0
simplify (s :*: N 0)   = N 0
simplify (f :+: g)     = simplify $ simplify f :+: simplify g
simplify (f :*: g)     = simplify f :*: simplify g
simplify (f :.: g)     = simplify f :.: simplify g
simplify (Der f)       = Der $ simplify f
simplify s = s

--------------------------------------------------------------------------------
-- Labelled enumeration (egf's) ------------------------------------------------
--------------------------------------------------------------------------------

facts :: [Integer]
facts = 1 : zipWith (*) [1..] facts

-- This is a nice idea, but the EGF library is too slow!!
--
-- instance Species (EGF.T Integer) where
--   singleton = EGF.fromCoeffs [0,1]
--   set       = EGF.fromCoeffs $ repeat 1
--   list      = EGF.fromCoeffs facts
--   o         = EGF.compose
--   nonEmpty  (EGF.Cons (_:xs)) = EGF.Cons (0:xs)
--   nonEmpty  x = x
--
-- labelled :: EGF.T Integer -> [Integer]
-- labelled = EGF.coeffs
--
-- Sigh.  Just compute explicitly with normal power series and
-- zip/unzip with factorial denominators as necessary.

newtype Labelled = Labelled (PowerSeries.T Rational)
  deriving (Additive.C, Ring.C, Differential.C, Show)

instance Species Labelled where
  singleton = Labelled $ PowerSeries.fromCoeffs [0,1]
  set       = Labelled $ PowerSeries.fromCoeffs (map (1%) facts)
  cycle     = Labelled $ PowerSeries.fromCoeffs (0 : map (1%) [1..])
  o (Labelled f) (Labelled g) = Labelled $ PowerSeries.compose f g
  nonEmpty (Labelled (PowerSeries.Cons (_:xs))) = Labelled (PowerSeries.Cons (0:xs))
  nonEmpty x = x

labelled :: Labelled -> [Integer]
labelled (Labelled f) = map numerator . zipWith (*) (map fromInteger facts) $ PowerSeries.coeffs f

--------------------------------------------------------------------------------
-- Cycle index series ----------------------------------------------------------
--------------------------------------------------------------------------------

instance Species (MVP.T Rational) where
  singleton = MVP.x 1
  set       = MVP.Cons . map partToMonomial . concatMap intPartitions $ [0..]

  cycle     = MVP.Cons . concatMap cycleMonomials $ [1..]

  o         = MVP.compose
  nonEmpty  p@(MVP.Cons (x:xs)) | Monomial.degree x == 0 = MVP.Cons xs
                                | otherwise              = p

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
  = Labelled . PowerSeries.fromCoeffs
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

--------------------------------------------------------------------------------
-- Generation of species -------------------------------------------------------
--------------------------------------------------------------------------------

-- This seems really ugly.  Is there a better way to do this?

-- data Structure a = Set [a]
--                  | Inl (Structure a)
--                  | Inr (Structure a)
--                  | Pair (Structure a) (Structure a)
--                  | Comp (Structure (Structure a))

-- instance Species ([a] -> [Structure a]) where
--   singleton []  = []
--   singleton [x] = [Set [x]]
--   singleton _   = []

--   set es        = [Set es]

--   list es       = map listToStructure (permutations es)

-- listToStructure :: [a] -> Structure a
-- listToStructure []     = Inl (Set [])
-- listToStructure (x:xs) = Inr (Pair (Set [x]) (listToStructure xs))

-- structureToList :: Structure a -> [a]
-- structureToList (Inl _) = []
-- structureToList (Inr (Pair (Set [x]) xs)) = x : structureToList xs
-- structureToList _ = error "invalid list structure"                      



-- newtype (f :+@ g) a = Sum  { unSum  :: Either (f a) (g a) }
--   deriving (Show)
-- newtype (f :*@ g) a = Prod { unProd :: (f a, g a) }
--   deriving (Show)
-- newtype (f :.@ g) a = Comp { unComp :: (f (g a)) }
--   deriving (Show)

-- data O
-- data I
-- data E
-- data X
-- data L
-- data (:+:) a b
-- data (:*:) a b
-- data (:.:) a b
-- data Der a
-- data (:@:) a b


-- splits :: [a] -> [([a],[a])]
-- splits []     = [([],[])]
-- splits (x:xs) = map (first (x:)) ss ++ map (second (x:)) ss
--   where ss = splits xs

-- -- power set
-- pSet :: [a] -> [([a],[a])]
-- pSet [] = [([],[])]
-- pSet (x:xs) = mapx first ++ mapx second 
--   where mapx which = map (which (x:)) $ pSet xs

-- partitions :: [a] -> [[[a]]]
-- partitions [] = [[]]
-- partitions (s:s') = do (sub,compl) <- pSet s'
--                        let firstSubset = s:sub
--                        map (firstSubset:) $ partitions compl

-- permutations :: [a] -> [[a]]
-- permutations [] = [[]]
-- permutations (x:xs) = undefined  -- XXX

-- over :: forall a f. Species f -> [a] -> [f a]
-- over O _   = []
-- over I []  = [[]]
-- over I _   = []
-- over E ls  = [ls]
-- over X [l] = [[l]]
-- over X _   = []
-- over L ls  = permutations ls
-- over (f :+: g) ls = map (Sum . Left) (f `over` ls) ++ map (Sum . Right) (g `over` ls) 
-- over (f :*: g) ls = [ Prod (x, y) | (s1,s2) <- splits ls
--                                   ,       x <- f `over` s1
--                                   ,       y <- g `over` s2 
--                     ]
-- over (f :.: g) ls = [ Comp y | p  <- partitions ls
--                              , xs <- mapM (g `over`) p
--                              , y  <- f `over` xs 
--                     ]
-- over (Der f) ls   = f `over` (undefined : ls)
-- over (f :@: g) ls = map Comp $ f `over` (g `over` ls)
-- over (NonEmpty f) [] = []
-- over (NonEmpty f) ls = f `over` ls
