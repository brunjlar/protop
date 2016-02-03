{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Protop.Identities
    ( Id
    , id'
    ) where

import Data.Proxy       (Proxy(..))
import Protop.Objects
import Protop.Morphisms
import Protop.Setoids

data Id a = Id a

id' :: IsObject a => a -> Id a
id' = Id

instance Show a => Show (Id a) where

    show (Id x) = "(id " ++ show x ++ ")"

instance IsObject a => IsMorphism (Id a) where

    type Source (Id a) = a
    type Target (Id a) = a
    onDomains _ = setId
    proxy' _    = Id $ proxy Proxy
