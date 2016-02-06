{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Protop.Exponentials
    ( (:->)(..)
    , Curry(..)
    ) where

import Data.Proxy       (Proxy(..))
import Protop.Morphisms
import Protop.Objects
import Protop.Products
import Protop.Setoids

infixr 1 :->

type CExp x y = (IsObject x, IsObject y)

data (:->) :: * -> * -> * where
    (:->) :: CExp x y => x -> y -> x :-> y
    
instance Show (x :-> y) where

    show (x :-> y) = "(" ++ show x ++ " -> " ++ show y ++ ")"

instance CExp x y => IsObject (x :-> y) where

    type Domain (x :-> y) = Functoid (Domain x) (Domain y)

    proxy _ = proxy Proxy :-> proxy Proxy

type CCurry x y f = ( IsObject x
                    , IsObject y
                    , IsMorphism f
                    , Source f ~ (x :* y)
                    )

data Curry :: * -> * -> * -> * where
    Curry :: CCurry x y f => x -> y -> f -> Curry x y f

instance Show (Curry x y f) where

    show (Curry x y f) = "(Curry " ++ show x ++ " " ++ show y ++ " " ++ show f ++ ")"

instance CCurry x y f => IsMorphism (Curry x y f) where

    type Source (Curry x y f) = x
    type Target (Curry x y f) = y :-> Target f

    onDomains (Curry _ _ f) = setCurry `onPoints` onDomains f
    proxy' _ = Curry (proxy Proxy) (proxy Proxy) (proxy' Proxy)
