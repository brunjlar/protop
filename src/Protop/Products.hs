{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

module Protop.Products
    ( (:*)(..)
    ) where

import Data.Proxy (Proxy(..))
import Protop.Objects

infixl 7 :*

data (:*) :: * -> * -> * where
   (:*) :: ( IsObject a
           , IsObject b
           ) => a -> b -> a :* b

instance Show (a :* b) where

    show (x :* y) = "(" ++ show x ++ " * " ++ show y ++ ")"

instance (IsObject a, IsObject b) => IsObject (a :* b) where

    type Domain (a :* b) = (Domain a, Domain b)

    proxy _ = proxy Proxy :* proxy Proxy
