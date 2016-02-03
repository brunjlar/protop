{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Protop.Objects
    ( IsObject(..)
    , Object(..)
    ) where

import Data.Function  (on)
import Data.Proxy     (Proxy(..))
import Protop.Setoids

class (Show a, IsSetoid (Domain a)) => IsObject a where

    type Domain a
    proxy :: Proxy a -> a

data Object where
    Object :: IsObject a => a -> Object

instance Show Object where

    show (Object p) = show p

instance Eq Object where

    (==) = (==) `on` show

instance Ord Object where

    compare = compare `on` show
