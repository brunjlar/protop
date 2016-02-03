{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

module Protop.Terminal
    ( T(..)
    , star
    , Terminal(..)
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

data Terminal :: * -> * where
    Terminal :: IsObject a => a -> Terminal a

instance Show (Terminal a) where

    show (Terminal x) = "!" ++ show x

instance IsObject a => IsMorphism (Terminal a) where

    type Source (Terminal a) = a
    type Target (Terminal a) = T

    onDomains _ = Functoid (const star) (const star)
    proxy' _    = Terminal $ proxy Proxy
