module Math.Combinatorics.Species.Generate where

instance ShowF [] where
  showF = show

newtype Const x a = Const x
instance Functor (Const x) where
  fmap _ (Const x) = Const x
instance (Show x) => Show (Const x a) where
  show (Const x) = show x
instance (Show x) => ShowF (Const x) where
  showF = show

newtype Identity a = Identity a
instance Functor Identity where
  fmap f (Identity x) = Identity (f x)
instance (Show a) => Show (Identity a) where
  show (Identity x) = show x
instance ShowF Identity where
  showF = show

newtype Sum f g a = Sum  { unSum  :: Either (f a) (g a) }
instance (Functor f, Functor g) => Functor (Sum f g) where
  fmap f (Sum (Left fa))  = Sum (Left (fmap f fa))
  fmap f (Sum (Right ga)) = Sum (Right (fmap f ga))
instance (Show (f a), Show (g a)) => Show (Sum f g a) where
  show (Sum x) = show x
instance (ShowF f, ShowF g) => ShowF (Sum f g) where
  showF (Sum (Left fa)) = "Left " ++ showF fa
  showF (Sum (Right ga)) = "Right " ++ showF ga

newtype Prod f g a = Prod { unProd :: (f a, g a) }
instance (Functor f, Functor g) => Functor (Prod f g) where
  fmap f (Prod (fa, ga)) = Prod (fmap f fa, fmap f ga)
instance (Show (f a), Show (g a)) => Show (Prod f g a) where
  show (Prod x) = show x
instance (ShowF f, ShowF g) => ShowF (Prod f g) where
  showF (Prod (fa, ga)) = "(" ++ showF fa ++ "," ++ showF ga ++ ")"

data Comp f g a = Comp { unComp :: (f (g a)) }
instance (Functor f, Functor g) => Functor (Comp f g) where
  fmap f (Comp fga) = Comp (fmap (fmap f) fga)
instance (Show (f (g a))) => Show (Comp f g a) where
  show (Comp x) = show x
instance (ShowF f, ShowF g) => ShowF (Comp f g) where
  showF (Comp fga) = showF (fmap (RawString . showF) fga)

newtype RawString = RawString String
instance Show RawString where
  show (RawString s) = s

newtype Cycle a = Cycle [a]
instance Functor Cycle where
  fmap f (Cycle xs) = Cycle (fmap f xs)
instance (Show a) => Show (Cycle a) where
  show (Cycle xs) = "{" ++ intercalate "," (map show xs) ++ "}"
instance ShowF Cycle where
  showF = show

data Star a = Star | Original a
instance Functor Star where
  fmap _ Star = Star
  fmap f (Original a) = Original (f a)
instance (Show a) => Show (Star a) where
  show Star = "*"
  show (Original a) = show a
instance ShowF Star where
  showF = show

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


data Structure a where
  Structure :: (ShowF f) => f a -> Structure a

instance (Show a) => Show (Structure a) where
  show (Structure t) = showF t

generate :: SpeciesAlg -> [a] -> [Structure a]
generate (SA s) xs = map Structure (generateF s xs)

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
