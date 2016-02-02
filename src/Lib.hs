{-# Language TypeFamilies #-}
{-# Language FlexibleInstances #-}
{-# Language FlexibleContexts #-}
{-# Language StandaloneDeriving #-}
{-# Language GADTs #-}

module Lib
    ( 
    ) where

class Setoid a where
    data Proofs a
    reflexivity :: a -> Proofs a
    lhs :: Proofs a -> a
    rhs :: Proofs a -> a
    symmetry :: Proofs a -> Proofs a
    transitivity :: Proofs a -> Proofs a -> Proofs a

newtype EqSet a = EqSet { runEqSet :: a } deriving Eq

instance Show a => Show (EqSet a) where

    show = show . runEqSet

instance Eq a => Setoid (EqSet a) where
    
    data Proofs (EqSet a) = EqProof { runEqProof :: a } deriving (Show, Eq)
    reflexivity = EqProof . runEqSet
    lhs = EqSet . runEqProof
    rhs = EqSet . runEqProof
    symmetry = id
    transitivity p q | p == q    = p 
                     | otherwise = error "incompatible proofs"

instance (Setoid a, Setoid b) => Setoid (a, b) where

    data Proofs (a, b) = Pair (Proofs a) (Proofs b)
    reflexivity (x, y) = Pair (reflexivity x) (reflexivity y)
    lhs (Pair p q) = (lhs p, lhs q)
    rhs (Pair p q) = (rhs p, rhs q)
    symmetry (Pair p q) = Pair (symmetry p) (symmetry q)
    transitivity (Pair p q) (Pair p' q') = Pair (transitivity p p') (transitivity q q')

deriving instance (Show (Proofs a), Show (Proofs b)) => Show (Proofs (a, b))
deriving instance (Eq (Proofs a), Eq (Proofs b)) => Eq (Proofs (a, b))

data Functoid :: * -> * -> * where
    Functoid :: (Setoid a, Setoid b) => (a -> b) -> (Proofs a -> Proofs b) -> Functoid a b

applyToPoint :: Functoid a b -> a -> b
applyToPoint (Functoid f _) = f

applyToProof :: Functoid a b -> Proofs a -> Proofs b
applyToProof (Functoid _ g) = g

instance Setoid b => Setoid (Functoid a b) where

    data Proofs (Functoid a b) = Extensional (Functoid a b) (Functoid a b) (a -> Proofs b)
    reflexivity f = Extensional f f $ reflexivity . (applyToPoint f)
    lhs (Extensional f _ _) = f
    rhs (Extensional _ g _) = g
    symmetry (Extensional f g p) = Extensional g f $ symmetry . p
    transitivity (Extensional f g p) (Extensional g' h q) = Extensional f h $ \x -> transitivity (p x) (q x)
