module Protop.Core.Reflexivities
    ( REFL(..)
    ) where

import Protop.Core.Morphisms
import Protop.Core.Proofs
import Protop.Core.Setoids
import Protop.Core.Singleton

data REFL :: * -> * where
    REFL :: IsMorphism a => a -> REFL a

instance IsMorphism a => Singleton (REFL a) where
    singleton = REFL singleton

instance Show (REFL a) where
    show (REFL x) = "(REFL " ++ show x ++ ")"

instance (Show a, IsMorphism a) => IsProof (REFL a) where
    type Lhs (REFL a) = a
    type Rhs (REFL a) = a
    proof (REFL f) x = reflexivity $ f .$ x
