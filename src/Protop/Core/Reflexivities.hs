{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Protop.Core.Reflexivities
    ( REFL(..)
    ) where

import Data.Proxy            (Proxy(..))
import Protop.Core.Morphisms
import Protop.Core.Proofs
import Protop.Core.Setoids

data REFL :: * -> * where
    REFL :: IsMorphism a => a -> REFL a

instance Show (REFL a) where

    show (REFL x) = "(REFL " ++ show x ++ ")"

instance (Show a, IsMorphism a) => IsProof (REFL a) where
    
    type Lhs (REFL a) = a
    type Rhs (REFL a) = a
    proof (REFL f) x = reflexivity $ f .$ x
    proxy'' _        = REFL $ proxy' Proxy
