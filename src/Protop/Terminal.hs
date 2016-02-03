{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Protop.Terminal
    ( T(..)
    , star
    , Terminal
    , t
    ) where

import Data.Proxy       (Proxy(..))
import Protop.Morphisms
import Protop.Objects
import Protop.Setoids

data T = T

instance Show T where

    show T = "T"

instance IsObject T where

    type Domain T = Set ()
    proxy _ = T

star :: Domain T
star = Set ()

data Terminal a = Terminal a

t :: IsObject a => a -> Terminal a
t = Terminal

instance Show a => Show (Terminal a) where

    show (Terminal x) = "!" ++ show x

instance IsObject a => IsMorphism (Terminal a) where

    type Source (Terminal a) = a
    type Target (Terminal a) = T
    onDomains _ = Functoid (const star) (const star)
    proxy' _    = t $ proxy Proxy
