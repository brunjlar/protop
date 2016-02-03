{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Protop.Terminal
    ( T(..)
    , star
    ) where

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
