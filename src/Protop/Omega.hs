{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Protop.Omega
    ( OmegaS(..)
    , OmegaP(..)
    , applyOmegaP
    , setTrue
    , Omega(..)
    , True'(..)
    ) where

import Data.Proxy     (Proxy(..))
import Data.Typeable  (Typeable, typeRep, cast, eqT, (:~:)(..))
import Protop.Morphisms
import Protop.Objects
import Protop.Setoids
import Protop.Terminal

data OmegaS :: * where
    OmegaS :: Typeable a => Proxy a -> OmegaS

instance Show OmegaS where

    show (OmegaS p) = "<" ++ show (typeRep p) ++ ">"

data OmegaP :: * where
    OmegaP :: (Typeable a, Typeable b) =>
                Proxy a -> Proxy b -> (a -> b) -> (b -> a) -> OmegaP

instance Show OmegaP where

    show (OmegaP p q _ _) =
        "<<" ++ show (typeRep p) ++ "=" ++ show (typeRep q) ++ ">>"

applyOmegaP :: (Typeable a, Typeable b) => OmegaP -> a -> Maybe b
applyOmegaP (OmegaP _ _ f _) x = cast x >>= cast . f

eqT' :: (Typeable a, Typeable b) => Proxy a -> Proxy b -> Maybe (a :~: b)
eqT' _ _ = eqT

instance IsSetoid OmegaS where

    type Proofs OmegaS = OmegaP

    reflexivity (OmegaS p)              = OmegaP p p id id
    symmetry _ (OmegaP p q f g)         = OmegaP q p g f
    transitivity _
                 x@(OmegaP p  q  f  g)
                 y@(OmegaP p' q' f' g') =
        case eqT' q p' of
            Nothing   -> error $ "incompatible proofs " ++ show x ++ " and " ++ show y
            Just Refl -> OmegaP p q' (f' . f) (g . g')

setTrue :: Functoid Star OmegaS
setTrue = let x = OmegaS (Proxy :: Proxy Star)
              p = reflexivity x
          in  Functoid (const x) (const p)

data Omega = Omega

instance Show Omega where

    show Omega = "Omega"

instance IsObject Omega where

    type Domain Omega = OmegaS

    proxy _ = Omega

data True' = True'

instance Show True' where

    show True' = "true"

instance IsMorphism True' where

    type Source True' = T
    type Target True' = Omega
    onDomains True' = setTrue
    proxy' _        = True'
