{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

module Protop.Identities
    ( Id(..)
    ) where

import Data.Proxy       (Proxy(..))
import Protop.Objects
import Protop.Morphisms
import Protop.Setoids

data Id :: * -> * where
    Id :: IsObject a => a -> Id a

instance Show (Id a) where

    show (Id x) = "(id " ++ show x ++ ")"

instance IsObject a => IsMorphism (Id a) where

    type Source (Id a) = a
    type Target (Id a) = a
    onDomains _ = setId
    proxy' _    = Id $ proxy Proxy
