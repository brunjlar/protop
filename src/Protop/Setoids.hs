{-# Language TypeFamilies #-}
{-# Language FlexibleInstances #-}
{-# Language FlexibleContexts #-}
{-# Language GADTs #-}
{-# Language ScopedTypeVariables #-}
{-# Language ConstraintKinds #-}
{-# Language StandaloneDeriving #-}
{-# Language TypeOperators #-}

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
    , setCurry
    , setUncurry
    , SetEql(..)
    , setInj
    , eqT'
    , eqT''
    ) where

import Control.Arrow   ((&&&))
import Data.Maybe      (fromMaybe)
import Data.Proxy      (Proxy(..))
import Data.Typeable   (Typeable, (:~:)(..), eqT, typeRep)
import Numeric.Natural (Natural)

class (Typeable a, Typeable (Proofs a)) => IsSetoid a where

    type Proofs a
    
    reflexivity  :: a -> Proofs a
    symmetry     :: Proxy a -> Proofs a -> Proofs a
    transitivity :: Proxy a -> Proofs a -> Proofs a -> Proofs a
    setLhs       :: Proofs a -> a
    setRhs       :: Proofs a -> a

data Functoid :: * -> * -> * where
    Functoid :: (IsSetoid a, IsSetoid b) => (a -> b) -> (Proofs a -> Proofs b) -> Functoid a b

onPoints :: Functoid a b -> a -> b
onPoints (Functoid f _) = f

onProofs :: Functoid a b -> Proofs a -> Proofs b
onProofs (Functoid _ g) = g

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
    setLhs (p, q)                  = (setLhs p, setLhs q)
    setRhs (p, q)                  = (setRhs p, setRhs q)

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
    setLhs _           = star
    setRhs _           = star

setT :: IsSetoid a => Functoid a Star
setT = Functoid (const star) (const star)

instance IsSetoid Natural where

    type Proofs Natural = Natural

    reflexivity  = id
    symmetry _   = id
    transitivity _ m n
        | m == n = m
        | otherwise = error $ "incompatible proofs: " ++ show m ++ " and " ++ show n
    setLhs n     = n
    setRhs n     = n
    
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

instance (IsSetoid a, IsSetoid b) => IsSetoid (Functoid a b) where

    type Proofs (Functoid a b) = (Functoid a b, Functoid a b, Proofs a -> Proofs b)

    reflexivity f                      = (f, f, onProofs f)
    symmetry _ (f, g, p)               = (g, f, symmetry (Proxy :: Proxy b) . p)
    transitivity _ (f, g, p) (_, h, q) = (f, h, \x -> transitivity (Proxy :: Proxy b) (p x) (q x))
    setLhs (f, _, _)                   = f
    setRhs (_, g, _)                   = g

type CCurry x y z = ( IsSetoid x
                    , IsSetoid y
                    , IsSetoid z
                    )

setCurry :: forall x y z. CCurry x y z =>
                Functoid (x, y) z -> Functoid x (Functoid y z)
setCurry g = Functoid h $ curry $ onProofs g where

    h :: x -> Functoid y z
    h x = Functoid h' h'' where

        h' :: y -> z
        h' y = g `onPoints` (x, y)

        h'' :: Proofs y -> Proofs z
        h'' py = g `onProofs` (reflexivity x, py)

setUncurry :: forall x y z. CCurry x y z =>
                Functoid (Functoid x (Functoid y z)) (Functoid (x, y) z)
setUncurry = Functoid f uncurry

  where

    f :: Functoid x (Functoid y z) -> Functoid (x, y) z
    f g = Functoid h h' where

        h :: (x, y) -> z
        h = uncurry $ onPoints . onPoints g

        h' :: (Proofs x, Proofs y) -> Proofs z
        h' = uncurry $ onProofs g

data SetEql :: * -> * -> * where
    SetEql :: (IsSetoid x, IsSetoid y) => x -> Proofs y -> SetEql x y

deriving instance ( IsSetoid x
                  , IsSetoid y
                  , Show x
                  , Show (Proofs y)
                  ) => Show (SetEql x y)

instance (IsSetoid x, IsSetoid y) => IsSetoid (SetEql x y) where

    type Proofs (SetEql x y) = Proofs x

    reflexivity (SetEql x _) = reflexivity x
    symmetry _               = symmetry (Proxy :: Proxy x)
    transitivity _           = transitivity (Proxy :: Proxy x)

setInj :: (IsSetoid x, IsSetoid y) => Functoid (SetEql x y) x
setInj = Functoid f f' where
    f (SetEql x _) = x
    f' = id

eqT' :: forall a b. (Typeable a, Typeable b) => a -> b -> a :~: b
eqT' _ _ = fromMaybe
            (error $ "incompatible types " ++
                show (typeRep (Proxy :: Proxy a)) ++ " and " ++
                show (typeRep (Proxy :: Proxy b)))
            eqT

eqT'' :: forall a b. (Typeable a, Typeable b) =>
            Proxy a -> Proxy b -> a :~: b
eqT'' pa pb = fromMaybe
                (error $ "incompatible types " ++
                    show (typeRep pa) ++ " and " ++
                    show (typeRep pb))
                eqT 
