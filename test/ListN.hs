{-# LANGUAGE TypeFamilies, EmptyDataDecls, FlexibleInstances, FlexibleContexts #-}
import NumericPrelude
import PreludeBase

import Math.Combinatorics.Species

newtype List5 a = List5 [a]

instance Show a => Show (List5 a) where
  show (List5 l) = show l

instance Iso List5 where
  type SType List5 = Prod Identity (Prod Identity (Prod Identity (Prod Identity Identity)))
  iso (Prod (Id a1) (Prod (Id a2) (Prod (Id a3) (Prod (Id a4) (Id a5))))) = List5 [a1,a2,a3,a4,a5]

data Z
data S n

type TOne = S Z
type Two = S TOne
type Three = S Two
type Four = S Three
type Five = S Four

data ListN n a = ListN [a]
cons :: a -> ListN n a -> ListN (S n) a
cons x (ListN xs) = ListN (x:xs)

instance Show a => Show (ListN n a) where
  show (ListN l) = show l

instance Iso (ListN Z) where
  type SType (ListN Z) = Set
  iso _ = ListN []

instance Iso (ListN n) => Iso (ListN (S n)) where
  type SType (ListN (S n)) = Prod Id (SType (ListN n))
  iso (Prod (Id x) xs) = x `cons` iso xs