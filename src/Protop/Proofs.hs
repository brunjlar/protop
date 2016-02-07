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
import Protop.Morphisms
import Protop.Objects
import Protop.Setoids

class ( Show a
      , IsMorphism (Lhs a)
      , IsMorphism (Rhs a)
      , Source (Lhs a) ~ Source (Rhs a)
      , Target (Lhs a) ~ Target (Rhs a)
      ) => IsProof a where

    type Lhs a
    type Rhs a

    proof   :: a -> Domain (PSource a) -> Proofs (Domain (PTarget a))
    proxy'' :: Proxy a -> a

type PSource a = Source (Lhs a)

type PTarget a = Target (Lhs a)

lhs :: forall a. IsProof a => a -> Lhs a
lhs _ = proxy' (Proxy :: Proxy (Lhs a)) 

rhs :: forall a. IsProof a => a -> Rhs a
rhs _ = proxy' (Proxy :: Proxy (Rhs a)) 

data Proof :: * -> * -> * where
    Proof :: IsProof a => a -> Proof (Lhs a) (Rhs a)

instance Show (Proof a b) where
    
    show (Proof p) = show p

instance Eq (Proof a b) where

    (==) = const $ const True

instance Ord (Proof a b) where

    compare = const $ const EQ

data PROOF :: * where
    PROOF :: IsProof a => a -> PROOF

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
