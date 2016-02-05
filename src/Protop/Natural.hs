{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}

module Protop.Natural
    ( N(..)
    , Zero(..)
    , Succ(..)
    , Rec(..)
    ) where

import Data.Proxy       (Proxy(..))
import Numeric.Natural  (Natural)
import Protop.Morphisms
import Protop.Objects
import Protop.Setoids
import Protop.Terminal

data N = N

instance Show N where

    show N = "N"

instance IsObject N where

    type Domain N = Natural
    proxy _ = N

data Zero = Zero

instance Show Zero where

    show Zero = "Zero"

instance IsMorphism Zero where

    type Source Zero = T
    type Target Zero = N
    onDomains _ = setZero
    proxy' _    = Zero

data Succ = Succ

instance Show Succ where

    show Succ = "Succ"

instance IsMorphism Succ where

    type Source Succ = N
    type Target Succ = N

    onDomains _ = setSucc
    proxy' _    = Succ

type CRec z s = ( IsMorphism z
                , IsMorphism s
                , Source z ~ T
                , Target z ~ Source s
                , Target s ~ Source s
                )

data Rec :: * -> * -> * where
    Rec :: CRec z s => z -> s -> Rec z s

instance Show (Rec z s) where

    show (Rec z s) = "(Rec " ++ show z ++ " " ++ show s ++ ")"

instance CRec z s => IsMorphism (Rec z s) where

    type Source (Rec z s) = N
    type Target (Rec z s) = Target z

    onDomains (Rec z s) = setRec (z .$ star) (onDomains s)
    proxy' _ = Rec (proxy' Proxy) (proxy' Proxy)
