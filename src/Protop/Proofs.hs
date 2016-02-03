{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Protop.Proofs
    ( IsProof(..)
    , PSource
    ) where

import Protop.Morphisms
import Protop.Objects
import Protop.Setoids

class ( IsMorphism (Lhs a)
      , IsMorphism (Rhs a)
      , Source (Lhs a) ~ Source (Rhs a)
      , Target (Lhs a) ~ Target (Rhs a)
      ) => IsProof a where

    type Lhs a
    type Rhs a
    proof :: a -> Domain (PSource a) -> Proofs (Domain (PTarget a))

type PSource a = Source (Lhs a)

type PTarget a = Target (Lhs a)
