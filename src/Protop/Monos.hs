{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module Protop.Monos
    ( CMono
    , MonoProof
    , Mono(..) 
    , monoId
    , monoComp
    ) where

import Protop.Compositions
import Protop.Identities
import Protop.Objects
import Protop.Morphisms
import Protop.Proofs
import Protop.Symmetries
import Protop.Transitivities

type CMono f t t' = ( IsMorphism t
                    , IsMorphism t'
                    , Source t ~ Source t'
                    , Target t ~ Target t'
                    , Target t ~ Source f
                    )

type MonoProof f =
    forall t t'. CMono f t t' =>
        t -> t' -> Proof (f :. t) (f :. t') -> Proof t t'

data Mono :: * -> * where
    Mono :: IsMorphism f => f -> MonoProof f -> Mono f

instance Show (Mono f) where

    show (Mono f _) = "Mono " ++ show f

monoId :: IsObject x => x -> Mono (Id x)
monoId x = Mono (Id x) $
    \t t' (Proof p) -> Proof $ SYMM (IDLEFT t) :> p :> IDLEFT t'

monoComp :: forall f g. ( IsMorphism f
                        , IsMorphism g
                        , Source f ~ Target g
                        ) => f -> g -> Mono (f :. g) -> Mono g
monoComp f g (Mono _ m) = Mono g m' where
    m' :: MonoProof g
    m' t t' (Proof p) = m t t' (Proof p') where
        p' = ASS f g t :> (f :.| p) :> SYMM (ASS f g t')
