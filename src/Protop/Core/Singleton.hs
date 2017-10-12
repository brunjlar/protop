{-# LANGUAGE DefaultSignatures #-}

module Protop.Core.Singleton
    ( Singleton (..)
    ) where

import GHC.Generics

class Singleton a where
    singleton :: a

    default singleton :: (Generic a, GSingleton (Rep a)) => a
    singleton = to gsingleton

class GSingleton f where
    gsingleton :: f a

instance GSingleton f => GSingleton (M1 i c f) where
    gsingleton = M1 gsingleton

instance GSingleton U1 where
    gsingleton = U1

instance Singleton a => GSingleton (K1 i a) where
    gsingleton = K1 singleton

instance (GSingleton f, GSingleton g) => GSingleton (f :*: g) where
    gsingleton = gsingleton :*: gsingleton
