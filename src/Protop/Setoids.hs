{-# Language TypeFamilies #-}
{-# Language FlexibleInstances #-}
{-# Language FlexibleContexts #-}
{-# Language GADTs #-}
{-# Language ScopedTypeVariables #-}
{-# Language ConstraintKinds #-}

module Protop.Setoids
    ( IsSetoid(..)
    , Functoid(..)
    , onPoints, onProofs
    , setId
    , setComp
    , setPr1
    , setPr2
    , setProd
    , Star
    , star
    , setT
    , setZero
    , setSucc
    , setRec
    ) where

import Control.Arrow   ((&&&))
import Data.Proxy      (Proxy(..))
import Data.Typeable   (Typeable)
import Numeric.Natural (Natural)

class (Typeable a, Typeable (Proofs a)) => IsSetoid a where

    type Proofs a
    
    reflexivity  :: a -> Proofs a
    symmetry     :: Proxy a -> Proofs a -> Proofs a
    transitivity :: Proxy a -> Proofs a -> Proofs a -> Proofs a

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

type Star = ()

star :: Star
star = ()

instance IsSetoid Star where

    type Proofs Star = Star

    reflexivity _      = star
    symmetry _ _       = star
    transitivity _ _ _ = star

setT :: IsSetoid a => Functoid a Star
setT = Functoid (const star) (const star)

instance IsSetoid Natural where

    type Proofs Natural = Natural

    reflexivity  = id
    symmetry _   = id
    transitivity _ m n
        | m == n = m
        | otherwise = error $ "incompatible proofs: " ++ show m ++ " and " ++ show n
    
setZero :: Functoid Star Natural
setZero = Functoid (const 0) (const 0)

setSucc :: Functoid Natural Natural
setSucc = Functoid succ succ

setRec :: forall a. IsSetoid a => a -> Functoid a a -> Functoid Natural a
setRec z s = Functoid r (reflexivity . r)

  where

    r :: Natural -> a
    r = loop z

    loop :: a -> Natural -> a
    loop x 0 = x
    loop x n = loop (s `onPoints` x) $ pred n
