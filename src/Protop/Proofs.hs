{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Protop.Proofs
    ( IsProof(..)
    , PSource
    , PTarget
    , lhs
    , rhs
    , Proof(..)
    , PROOF(..)
    ) where

import Data.Monoid      ((<>))
import Data.Proxy       (Proxy(..))
import Data.Typeable    (Typeable)
import Protop.Morphisms
import Protop.Objects
import Protop.Setoids

class ( Show p
      , Typeable p
      , IsMorphism (Lhs p)
      , IsMorphism (Rhs p)
      , Source (Lhs p) ~ Source (Rhs p)
      , Target (Lhs p) ~ Target (Rhs p)
      ) => IsProof p where

    type Lhs p
    type Rhs p

    proof   :: p -> Domain (PSource p) -> Proofs (Domain (PTarget p))
    proxy'' :: Proxy p -> p

type PSource p = Source (Lhs p)

type PTarget p = Target (Lhs p)

lhs :: forall p. IsProof p => p -> Lhs p
lhs _ = proxy' (Proxy :: Proxy (Lhs p)) 

rhs :: forall p. IsProof p => p -> Rhs p
rhs _ = proxy' (Proxy :: Proxy (Rhs p)) 

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
