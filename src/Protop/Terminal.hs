{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}

module Protop.Terminal
    ( T(..)
    , Terminal(..)
    , TERMINAL(..)
    ) where

import Data.Proxy       (Proxy(..))
import Protop.Morphisms
import Protop.Objects
import Protop.Proofs
import Protop.Setoids

data T = T

instance Show T where

    show T = "T"

instance IsObject T where

    type Domain T = Set ()

    proxy _ = T

data Terminal :: * -> * where
    Terminal :: IsObject a => a -> Terminal a

instance Show (Terminal a) where

    show (Terminal x) = "!" ++ show x

instance IsObject a => IsMorphism (Terminal a) where

    type Source (Terminal a) = a
    type Target (Terminal a) = T

    onDomains _ = setT
    proxy' _    = Terminal $ proxy Proxy

type CTERMINAL a = (IsMorphism a , Target a ~ T)

data TERMINAL :: * -> * where
    TERMINAL :: CTERMINAL a => a -> TERMINAL a

instance Show (TERMINAL a) where

    show (TERMINAL f) = "!" ++ show f

instance CTERMINAL a => IsProof (TERMINAL a) where

    type Lhs (TERMINAL a) = a
    type Rhs (TERMINAL a) = Terminal (Source a)
    proof = const $ const star 
    proxy'' _ = TERMINAL $ proxy' Proxy
