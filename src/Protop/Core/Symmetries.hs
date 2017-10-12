module Protop.Core.Symmetries
    ( SYMM(..)
    ) where

import Data.Proxy            (Proxy(..))
import Protop.Core.Proofs
import Protop.Core.Setoids
import Protop.Core.Singleton

data SYMM :: * -> * where
    SYMM :: IsProof a => a -> SYMM a

instance IsProof a => Singleton (SYMM a) where
    singleton = SYMM singleton

instance Show (SYMM a) where
    show (SYMM p) = "~" ++ show p

instance IsProof a => IsProof (SYMM a) where
    type Lhs (SYMM a) = Rhs a
    type Rhs (SYMM a) = Lhs a
    proof (SYMM p) x = symmetry (Proxy :: Proxy (DTARGET a)) $ proof p x
