{-# LANGUAGE NoImplicitPrelude 
           , GADTs
           , FlexibleInstances
           , GeneralizedNewtypeDeriving
           , EmptyDataDecls
           , TypeOperators
           , TypeFamilies
           , FlexibleContexts
           , MultiParamTypeClasses
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
import Control.Arrow ((&&&), first, second)
import Data.List (genericReplicate, genericDrop, groupBy, sort, intercalate)
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

  -- some derived species, in the class so we can have specialized
  -- implementations.
  list      :: s
  list = oneHole cycle


-- Some convenient synonyms and derived operations.
pointed, oneHole :: (Species s) => s -> s  
pointed = (singleton *) . Differential.differentiate
oneHole = Differential.differentiate

madeOf :: Species s => s -> s -> s
madeOf = o

x, singletons, e, sets, cycles, lists :: Species s => s
x          = singleton
singletons = singleton
e          = set
sets       = set
cycles     = cycle
lists      = list

-- More derived species.
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

data Z
data S n
data X
data (:+:) f g
data (:*:) f g
data (:.:) f g
data Der f
data E
data C
data NonEmpty f

data SpeciesAlgT s where
   O        :: SpeciesAlgT Z
   I        :: SpeciesAlgT (S Z)
   X        :: SpeciesAlgT X
   (:+:)    :: SpeciesAlgT f -> SpeciesAlgT g -> SpeciesAlgT (f :+: g)
   (:*:)    :: SpeciesAlgT f -> SpeciesAlgT g -> SpeciesAlgT (f :*: g)
   (:.:)    :: SpeciesAlgT f -> SpeciesAlgT g -> SpeciesAlgT (f :.: g)
   Der      :: SpeciesAlgT f -> SpeciesAlgT (Der f)
   E        :: SpeciesAlgT E
   C        :: SpeciesAlgT C
   NonEmpty :: SpeciesAlgT f -> SpeciesAlgT (NonEmpty f)
--     deriving (Show)

-- existential wrapper
data SpeciesAlg where
  SA :: SpeciesAlgT s -> SpeciesAlg

instance Additive.C SpeciesAlg where
  zero   = SA O
  (SA f) + (SA g) = SA (f :+: g)
  negate = error "negation is not implemented yet!  wait until virtual species..."

instance Ring.C SpeciesAlg where
  (SA f) * (SA g) = SA (f :*: g)
  one = SA I

instance Differential.C SpeciesAlg where
  differentiate (SA f) = SA (Der f)

instance Species SpeciesAlg where
  singleton = SA X
  set       = SA E
  cycle     = SA C
  o (SA f) (SA g) = SA (f :.: g)
  nonEmpty (SA f) = SA (NonEmpty f)

reify :: SpeciesAlg -> SpeciesAlg
reify = id

-- reflect :: Species s => SpeciesAlg -> s
-- reflect = undefined -- XXX

-- -- This is the basic idea: to do this right, we really want a more
-- --   sophisticated rewriting system.
-- simplify :: SpeciesAlg -> SpeciesAlg
-- simplify (N n :+: N m) = N (n+m)
-- simplify (N n :*: N m) = N (n*m)
-- simplify (N 0 :+: s)   = simplify s
-- simplify (s :+: N 0)   = simplify s
-- simplify (N 0 :*: s)   = N 0
-- simplify (s :*: N 0)   = N 0
-- simplify (f :+: g)     = simplify $ simplify f :+: simplify g
-- simplify (f :*: g)     = simplify f :*: simplify g
-- simplify (f :.: g)     = simplify f :.: simplify g
-- simplify (Der f)       = Der $ simplify f
-- simplify s = s

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

newtype Const x a = Const x
instance (Show x) => Show (Const x a) where
  show (Const x) = show x

newtype Identity a = Identity a
instance (Show a) => Show (Identity a) where
  show (Identity x) = show x

newtype Sum f g a = Sum  { unSum  :: Either (f a) (g a) }
instance (Show (f a), Show (g a)) => Show (Sum f g a) where
  show (Sum x) = show x

newtype Prod f g a = Prod { unProd :: (f a, g a) }
instance (Show (f a), Show (g a)) => Show (Prod f g a) where
  show (Prod x) = show x

newtype Comp f g a = Comp { unComp :: (f (g a)) }
instance (Show (f (g a))) => Show (Comp f g a) where
  show (Comp x) = show x

newtype Cycle a = Cycle [a]
instance (Show a) => Show (Cycle a) where
  show (Cycle xs) = "{" ++ intercalate "," (map show xs) ++ "}"
instance Functor Cycle where
  fmap f (Cycle xs) = Cycle (fmap f xs)

data Star a = Star | Original a
instance (Show a) => Show (Star a) where
  show Star = "*"
  show (Original a) = show a

type family StructureF t :: * -> *
type instance StructureF Z            = Const Integer
type instance StructureF (S s)        = Const Integer
type instance StructureF X            = Identity
type instance StructureF (f :+: g)    = Sum (StructureF f) (StructureF g)
type instance StructureF (f :*: g)    = Prod (StructureF f) (StructureF g)
type instance StructureF (f :.: g)    = Comp (StructureF f) (StructureF g)
type instance StructureF (Der f)      = Comp (StructureF f) Star
type instance StructureF E            = []
type instance StructureF C            = Cycle
type instance StructureF (NonEmpty f) = StructureF f

generateF :: SpeciesAlgT s -> [a] -> [StructureF s a]
generateF O _   = []
generateF I []  = [Const 1]
generateF I _   = []
generateF X [x] = [Identity x]
generateF X _   = []
generateF (f :+: g) xs = map (Sum . Left ) (generateF f xs) 
                      ++ map (Sum . Right) (generateF g xs)
generateF (f :*: g) xs = [ Prod (x, y) | (s1,s2) <- splits xs
                                       ,       x <- generateF f s1
                                       ,       y <- generateF g s2
                         ]
generateF (f :.: g) xs = [ Comp y | p  <- sPartitions xs
                                  , xs <- mapM (generateF g) p
                                  , y  <- generateF f xs
                         ]
generateF (Der f) xs = map Comp $ generateF f (Star : map Original xs)
generateF E xs = [xs]
generateF C [] = []
generateF C (x:xs) = map (Cycle . (x:)) (permutations xs)
generateF (NonEmpty f) [] = []
generateF (NonEmpty f) xs = generateF f xs

-- power set
pSet :: [a] -> [([a],[a])]
pSet [] = [([],[])]
pSet (x:xs) = mapx first ++ mapx second 
  where mapx which = map (which (x:)) $ pSet xs

sPartitions :: [a] -> [[[a]]]
sPartitions [] = [[]]
sPartitions (s:s') = do (sub,compl) <- pSet s'
                        let firstSubset = s:sub
                        map (firstSubset:) $ sPartitions compl

splits :: [a] -> [([a],[a])]
splits []     = [([],[])]
splits (x:xs) = map (first (x:)) ss ++ map (second (x:)) ss
  where ss = splits xs

permutations :: [a] -> [[a]]
permutations [] = [[]]
permutations xs = [ y:p | (y,ys) <- select xs
                        , p      <- permutations ys
                  ]

select :: [a] -> [(a,[a])]
select [] = []
select (x:xs) = (x,xs) : map (second (x:)) (select xs)


-- data Structure where
--   Structure :: (Show t) => t -> Structure

-- generate :: SpeciesAlg -> [a] -> [Structure]
-- generate (SA s) xs = map Structure (generateF s xs)

class Iso f g where
  iso :: f a -> g a

instance Iso (Comp Cycle Star) [] where
  iso (Comp (Cycle (_:xs))) = map (\(Original x) -> x) xs

instance (Iso f g, Functor h) => Iso (Comp h f) (Comp h g) where
  iso (Comp h) = Comp (fmap iso h)

instance (Iso f1 f2, Iso g1 g2) => Iso (Sum f1 g1) (Sum f2 g2) where
  iso (Sum (Left x)) = Sum (Left (iso x))
  iso (Sum (Right x)) = Sum (Right (iso x))

instance (Iso f1 f2, Iso g1 g2) => Iso (Prod f1 g1) (Prod f2 g2) where
  iso (Prod (x,y)) = Prod (iso x, iso y)

generateFI :: (Iso (StructureF s) f) => SpeciesAlgT s -> [a] -> [f a]
generateFI s xs = map iso $ generateF s xs
