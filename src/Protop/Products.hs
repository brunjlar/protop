{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}

module Protop.Products
    ( (:*)(..)
    , Pr1(..)
    , Pr2(..)
    ) where

import Data.Proxy (Proxy(..))
import Protop.Morphisms
import Protop.Objects
import Protop.Setoids

infixl 7 :*

type CProd a b = (IsObject a, IsObject b)

data (:*) :: * -> * -> * where
   (:*) :: CProd a b => a -> b -> a :* b

instance Show (a :* b) where

    show (x :* y) = "(" ++ show x ++ " * " ++ show y ++ ")"

instance CProd a b => IsObject (a :* b) where

    type Domain (a :* b) = (Domain a, Domain b)

    proxy _ = proxy Proxy :* proxy Proxy

data Pr1 :: * -> * -> * where
    Pr1 :: CProd a b => a -> b -> Pr1 a b

instance Show (Pr1 a b) where

    show (Pr1 x y) = "(pr1 " ++ show x ++ " " ++ show y ++ ")"

instance CProd a b => IsMorphism (Pr1 a b) where

    type Source (Pr1 a b) = a :* b
    type Target (Pr1 a b) = a
    onDomains _ = setPr1
    proxy' _ = Pr1 (proxy Proxy) (proxy Proxy)

data Pr2 :: * -> * -> * where
    Pr2 :: CProd a b => a -> b -> Pr2 a b

instance Show (Pr2 a b) where

    show (Pr2 x y) = "(pr2 " ++ show x ++ " " ++ show y ++ ")"

instance CProd a b => IsMorphism (Pr2 a b) where

    type Source (Pr2 a b) = a :* b
    type Target (Pr2 a b) = b
    onDomains _ = setPr2
    proxy' _ = Pr2 (proxy Proxy) (proxy Proxy)
