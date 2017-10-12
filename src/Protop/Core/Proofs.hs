module Protop.Core.Proofs
    ( IsProof(..)
    , SOURCE
    , TARGET
    , DSOURCE
    , DTARGET
    , PSOURCE
    , PTARGET
    , lhs
    , rhs
    , Proof(..)
    , PROOF(..)
    ) where

import Data.Monoid           ((<>))
import Data.Typeable         (Typeable)
import Protop.Core.Morphisms
import Protop.Core.Objects
import Protop.Core.Setoids
import Protop.Core.Singleton

class ( Show p
      , Typeable p
      , IsMorphism (Lhs p)
      , IsMorphism (Rhs p)
      , Source (Lhs p) ~ Source (Rhs p)
      , Target (Lhs p) ~ Target (Rhs p)
      , Singleton p
      ) => IsProof p where
    type Lhs p
    type Rhs p
    proof   :: p -> Domain (SOURCE p) -> Proofs (Domain (TARGET p))

type SOURCE p  = Source (Lhs p)
type TARGET p  = Target (Lhs p)
type DSOURCE p = Domain (SOURCE p)
type DTARGET p = Domain (TARGET p)
type PSOURCE p = Proofs (DSOURCE p)
type PTARGET p = Proofs (DTARGET p)

lhs :: IsProof p => p -> Lhs p
lhs _ = singleton

rhs :: IsProof p => p -> Rhs p
rhs _ = singleton

data Proof :: * -> * -> * where
    Proof :: IsProof p => p -> Proof (Lhs p) (Rhs p)

instance Show (Proof f g) where

    show (Proof p) = show p

instance Eq (Proof f g) where

    (==) = const $ const True

instance Ord (Proof f g) where

    compare = const $ const EQ

data PROOF :: * where
    PROOF :: IsProof p => p -> PROOF

instance Show PROOF where

    show (PROOF p) = show p

instance Eq PROOF where

    PROOF p == PROOF q =
        (MORPHISM (lhs p) == MORPHISM (lhs q)) &&
        (MORPHISM (rhs p) == MORPHISM (rhs q))

instance Ord PROOF where

    PROOF p `compare` PROOF q =
        (MORPHISM (lhs p) `compare` MORPHISM (lhs q)) <>
        (MORPHISM (rhs p) `compare` MORPHISM (rhs q))
