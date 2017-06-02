module Protop.Core.Identities
    ( Id(..)
    , IDLEFT(..)
    , IDRIGHT(..)
    ) where

import Data.Proxy               (Proxy(..))
import Protop.Core.Compositions
import Protop.Core.Objects
import Protop.Core.Morphisms
import Protop.Core.Proofs
import Protop.Core.Setoids

data Id :: * -> * where
    Id :: IsObject a => a -> Id a

instance Show (Id a) where

    show (Id x) = "(id " ++ show x ++ ")"

instance IsObject a => IsMorphism (Id a) where

    type Source (Id a) = a
    type Target (Id a) = a

    onDomains _ = setId
    proxy' _    = Id $ proxy Proxy

data IDLEFT :: * -> * where
    IDLEFT :: IsMorphism a => a -> IDLEFT a

instance Show (IDLEFT a) where

    show (IDLEFT f) = "(IDLEFT " ++ show f ++ ")"

instance IsMorphism a => IsProof (IDLEFT a) where

    type Lhs (IDLEFT a) = Id (Target a) :. a
    type Rhs (IDLEFT a) = a

    proof (IDLEFT f) x = reflexivity $ f .$ x
    proxy'' _          = IDLEFT $ proxy' Proxy

data IDRIGHT :: * -> * where
    IDRIGHT :: IsMorphism a => a -> IDRIGHT a

instance Show (IDRIGHT a) where

    show (IDRIGHT f) = "(IDRIGHT " ++ show f ++ ")"

instance IsMorphism a => IsProof (IDRIGHT a) where

    type Lhs (IDRIGHT a) = a :. Id (Source a)
    type Rhs (IDRIGHT a) = a

    proof (IDRIGHT f) x = reflexivity $ f .$ x
    proxy'' _          = IDRIGHT $ proxy' Proxy
