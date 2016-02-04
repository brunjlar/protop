{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Protop.Natural
    ( N(..)
    , Zero(..)
    , Succ(..)
    ) where

import Numeric.Natural
import Protop.Morphisms
import Protop.Objects
import Protop.Setoids
import Protop.Terminal

data N = N

instance Show N where

    show N = "N"

instance IsObject N where

    type Domain N = Set Natural
    proxy _ = N

data Zero = Zero

instance Show Zero where

    show Zero = "Zero"

instance IsMorphism Zero where

    type Source Zero = T
    type Target Zero = N
    onDomains _ = setFun (const $ Set 0)
    proxy' _    = Zero

data Succ = Succ

instance Show Succ where

    show Succ = "Succ"

instance IsMorphism Succ where

    type Source Succ = N
    type Target Succ = N
    onDomains _ = setFun $ Set . succ
    proxy' _    = Succ
