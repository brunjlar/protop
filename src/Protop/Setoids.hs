{-# Language TypeFamilies #-}
{-# Language FlexibleInstances #-}
{-# Language FlexibleContexts #-}
{-# Language StandaloneDeriving #-}
{-# Language GADTs #-}
{-# Language ScopedTypeVariables #-}

module Protop.Setoids
    ( IsSetoid(..)
    , Set(..)
    , Functoid(..)
    , onPoints, onProofs
    ) where

import Data.Proxy (Proxy(..))

class IsSetoid a where
    type Proofs a
    reflexivity  :: a -> Proofs a
    symmetry     :: Proxy a -> Proofs a -> Proofs a
    transitivity :: Proxy a -> Proofs a -> Proofs a -> Proofs a

data Set :: * -> * where
    Set :: Eq a => a -> Set a

deriving instance Show a => Show (Set a)
deriving instance Eq a => Eq (Set a)

instance IsSetoid (Set a) where
    
    type Proofs (Set a) = Set a
    reflexivity = id
    symmetry _ = id
    transitivity _ (Set x) (Set y) | x == y    = Set x
                                   | otherwise = error "incompatible proofs"

instance (IsSetoid a, IsSetoid b) => IsSetoid (a, b) where

    type Proofs (a, b) = (Proofs a, Proofs b)
    reflexivity (x, y) = (reflexivity x, reflexivity y)
    symmetry _ (p, q) = (symmetry (Proxy :: Proxy a) p, symmetry (Proxy :: Proxy b) q)
    transitivity _ (p, q) (p', q') = (transitivity (Proxy :: Proxy a) p p', transitivity (Proxy :: Proxy b) q q')

data Functoid :: * -> * -> * where
    Functoid :: (IsSetoid a, IsSetoid b) => (a -> b) -> (Proofs a -> Proofs b) -> Functoid a b

onPoints :: Functoid a b -> a -> b
onPoints (Functoid f _) = f

onProofs :: Functoid a b -> Proofs a -> Proofs b
onProofs (Functoid _ g) = g

instance IsSetoid b => IsSetoid (Functoid a b) where

    type Proofs (Functoid a b) = a -> Proofs b
    reflexivity f = reflexivity . (f `onPoints`)
    symmetry _ p = symmetry (Proxy :: Proxy b) . p
    transitivity _ p q = \x -> transitivity (Proxy :: Proxy b) (p x) (q x)
