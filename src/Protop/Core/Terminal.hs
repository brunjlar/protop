module Protop.Core.Terminal
    ( T(..)
    , Terminal(..)
    , TERMINAL(..)
    ) where

import Data.Proxy            (Proxy(..))
import Protop.Core.Morphisms
import Protop.Core.Objects
import Protop.Core.Proofs
import Protop.Core.Setoids

data T = T

instance Show T where

    show T = "T"

instance IsObject T where

    type Domain T = Star

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
