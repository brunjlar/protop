{-# Language TypeFamilies #-}
{-# Language FlexibleInstances #-}
{-# Language FlexibleContexts #-}
{-# Language StandaloneDeriving #-}
{-# Language GADTs #-}
{-# Language ScopedTypeVariables #-}
{-# Language ConstraintKinds #-}

module Protop.Setoids
    ( IsSetoid(..)
    , Set(..)
    , Functoid(..)
    , onPoints, onProofs
    , setId
    , setComp
    , setFun
    , setPr1
    , setPr2
    , setProd
    , star
    , setT
    ) where

import Control.Arrow ((&&&))
import Data.Proxy    (Proxy(..))
import Data.Typeable (Typeable)

class (Typeable a, Typeable (Proofs a)) => IsSetoid a where

    type Proofs a

    reflexivity  :: a -> Proofs a
    symmetry     :: Proxy a -> Proofs a -> Proofs a
    transitivity :: Proxy a -> Proofs a -> Proofs a -> Proofs a

data Set :: * -> * where
    Set :: Eq a => a -> Set a

deriving instance Show a => Show (Set a)
deriving instance Eq a => Eq (Set a)

instance Typeable a => IsSetoid (Set a) where
    
    type Proofs (Set a) = Set a

    reflexivity     = id
    symmetry _      = id
    transitivity _ (Set x) (Set y)
        | x == y    = Set x
        | otherwise = error "incompatible proofs"

data Functoid :: * -> * -> * where
    Functoid :: (IsSetoid a, IsSetoid b) => (a -> b) -> (Proofs a -> Proofs b) -> Functoid a b

onPoints :: Functoid a b -> a -> b
onPoints (Functoid f _) = f

onProofs :: Functoid a b -> Proofs a -> Proofs b
onProofs (Functoid _ g) = g

instance (Typeable a, IsSetoid b) => IsSetoid (Functoid a b) where

    type Proofs (Functoid a b) = a -> Proofs b

    reflexivity f        = reflexivity . (f `onPoints`)
    symmetry _ p         = symmetry (Proxy :: Proxy b) . p
    transitivity _ p q x = transitivity (Proxy :: Proxy b) (p x) (q x)

setId :: IsSetoid a => Functoid a a
setId = Functoid id id

setComp :: forall a b c. Functoid b c -> Functoid a b -> Functoid a c
setComp (Functoid f p) (Functoid g q) = Functoid (f . g) (p . q)

setFun :: forall a b. (Eq a, Typeable a, IsSetoid b) => (a -> b) -> Functoid (Set a) b
setFun f = Functoid (\(Set x) -> f x) $ \(Set x) -> reflexivity $ f x

type CProd a b = (IsSetoid a, IsSetoid b)

instance CProd a b => IsSetoid (a, b) where

    type Proofs (a, b)             = (Proofs a, Proofs b)

    reflexivity (x, y)             = (reflexivity x, reflexivity y)
    symmetry _ (p, q)              = (symmetry (Proxy :: Proxy a) p, symmetry (Proxy :: Proxy b) q)
    transitivity _ (p, q) (p', q') = (transitivity (Proxy :: Proxy a) p p', transitivity (Proxy :: Proxy b) q q')

setPr1 :: CProd a b => Functoid (a, b) a
setPr1 = Functoid fst fst

setPr2 :: CProd a b => Functoid (a, b) b
setPr2 = Functoid snd snd

setProd :: Functoid a b -> Functoid a c -> Functoid a (b, c)
setProd (Functoid f f') (Functoid g g') = Functoid (f &&& g) (f' &&& g')

star :: Set ()
star = Set ()

setT :: IsSetoid a => Functoid a (Set ())
setT = Functoid (const star) (const star)
