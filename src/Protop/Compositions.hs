{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Protop.Compositions
    ( (:<<)
    , (<<)
    ) where

import Data.Proxy       (Proxy(..))
import Protop.Morphisms
import Protop.Setoids

infixr 9 :<<

data a :<< b = a :<< b

infixr 9 <<

(<<) :: (IsMorphism a, IsMorphism b, Source a ~ Target b) => a -> b -> a :<< b
(<<) = (:<<)

instance (Show a, Show b) => Show (a :<< b) where

    show (f :<< g) = "(" ++ show f ++ " . " ++ show g ++ ")"

instance (IsMorphism a, IsMorphism b, Source a ~ Target b) => IsMorphism (a :<< b) where

    type Source (a :<< b) = Source b
    type Target (a :<< b) = Target a
    onDomains (f :<< g) = setComp (onDomains f) (onDomains g)
    proxy' _            = proxy' Proxy :<< proxy' Proxy
