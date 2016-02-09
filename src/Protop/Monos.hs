{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module Protop.Monos
    ( MonoTest(..)
    , MonoTest1(..)
    , MonoTest2(..)
    , MONOTEST(..)
    , MONOAPPLY(..)
    , setConst
    , monoIsInjective
    , monoId
    , monoComp
    , monoT
    , eqT'
    ) where

import Data.Proxy            (Proxy(..))
import Data.Typeable         ((:~:)(..))
import Protop.Compositions
import Protop.Identities
import Protop.Objects
import Protop.Morphisms
import Protop.Proofs
import Protop.Setoids
import Protop.Symmetries
import Protop.Terminal
import Protop.Transitivities

data MPoint :: * -> * where

    MPoint :: ( IsMorphism f
              , IsSetoid z
              ) => f ->
                   Functoid z (Domain (Source f)) ->
                   Functoid z (Domain (Source f)) ->
                   (z -> Proofs (Domain (Target f))) ->
                   Proxy z -> z -> MPoint f

data MProof :: * -> * where

    MProof :: ( IsMorphism f
              , IsSetoid z
              ) => f ->
                   Functoid z (Domain (Source f)) ->
                   Functoid z (Domain (Source f)) ->
                   (z -> Proofs (Domain (Target f))) ->
                   Proxy z -> Proofs z -> MProof f

instance IsMorphism f => IsSetoid (MPoint f) where

    type Proofs (MPoint f) = MProof f

    reflexivity (MPoint f t t' p r x)     = MProof f t t' p r $ reflexivity x
    symmetry _ (MProof f t t' p r px)     = MProof f t t' p r $ symmetry r px
    transitivity _ (MProof f t t' p  r px)
                   (MProof _ s s' p' _ qx) =
        case (eqT' t s, eqT' t' s', eqT' p p') of
           (Refl, Refl, Refl) ->
                MProof f t t' p r $ transitivity r px qx

data MonoTest :: * -> * where

    MonoTest :: IsMorphism f => f -> MonoTest f

instance Show (MonoTest f) where

    show (MonoTest f) = "(MonoTest " ++ show f ++ ")"

instance IsMorphism f => IsObject (MonoTest f) where

    type Domain (MonoTest f) = MPoint f

    proxy _ = MonoTest (proxy' Proxy)

data MonoTest1 :: * -> * where

    MonoTest1 :: IsMorphism f => f -> MonoTest1 f

instance Show (MonoTest1 f) where

    show (MonoTest1 f) = "(MonoTest1 " ++ show f ++ ")"

instance IsMorphism f => IsMorphism (MonoTest1 f) where

    type Source (MonoTest1 f) = MonoTest f
    type Target (MonoTest1 f) = Source f

    onDomains (MonoTest1 f) = Functoid g g' where
        g (MPoint f' t _ _ _ x) =
            case eqT' f f' of Refl -> t `onPoints` x
        g' (MProof f' t _ _ _ px) =
            case eqT' f f' of Refl -> t `onProofs` px

    proxy' _ = MonoTest1 (proxy' Proxy)

data MonoTest2 :: * -> * where

    MonoTest2 :: IsMorphism f => f -> MonoTest2 f

instance Show (MonoTest2 f) where

    show (MonoTest2 f) = "(MonoTest2 " ++ show f ++ ")"

instance IsMorphism f => IsMorphism (MonoTest2 f) where

    type Source (MonoTest2 f) = MonoTest f
    type Target (MonoTest2 f) = Source f

    onDomains (MonoTest2 f) = Functoid g g' where
        g (MPoint f' _ t' _ _ x) =
            case eqT' f f' of Refl -> t' `onPoints` x
        g' (MProof f' _ t' _ _ px) =
            case eqT' f f' of Refl -> t' `onProofs` px

    proxy' _ = MonoTest2 (proxy' Proxy)

data MONOTEST :: * -> * where

    MONOTEST :: IsMorphism f => f -> MONOTEST f

instance Show (MONOTEST f) where

    show (MONOTEST f) = "(MONOTEST " ++ show f ++ ")"

instance IsMorphism f => IsProof (MONOTEST f) where

    type Lhs (MONOTEST f) = f :. MonoTest1 f
    type Rhs (MONOTEST f) = f :. MonoTest2 f 

    proof (MONOTEST f) (MPoint f' _ _ p _ x) =
        case eqT' f f' of Refl -> p x

    proxy'' _ = MONOTEST (proxy' Proxy)

type CMONOAPPLY f t t' p p' = ( IsMorphism f
                              , IsMorphism t
                              , IsMorphism t'
                              , IsProof p
                              , IsProof p'
                              , Source t ~ Source t'
                              , Target t ~ Target t'
                              , Target t ~ Source f
                              , Lhs p ~ MonoTest1 f
                              , Rhs p ~ MonoTest2 f
                              , Lhs p' ~ (f :. t)
                              , Rhs p' ~ (f :. t')
                              )

data MONOAPPLY :: * -> * -> * -> * -> * -> * where

    MONOAPPLY :: CMONOAPPLY f t t' p p' =>
        f -> t -> t' -> p -> p' -> MONOAPPLY f t t' p p'

instance Show (MONOAPPLY f t t' p p') where

    show (MONOAPPLY f t t' p p') =
        "(MONOAPPLY " ++ show f ++ " " ++ show t ++ " " ++
        show t' ++ " " ++ show p ++ " " ++ show p' ++ ")"

instance CMONOAPPLY f t t' p p' => IsProof (MONOAPPLY f t t' p p') where
   
    type Lhs (MONOAPPLY f t t' p p') = t
    type Rhs (MONOAPPLY f t t' p p') = t'

    proof (MONOAPPLY f t t' p p') x = proof p $
        MPoint f (onDomains t) (onDomains t') (proof p') Proxy x

    proxy'' _ = MONOAPPLY (proxy' Proxy)
                          (proxy' Proxy)
                          (proxy' Proxy)
                          (proxy'' Proxy)
                          (proxy'' Proxy)

setConst :: IsSetoid x => x -> Functoid Star x
setConst  x = Functoid (const x) (const $ reflexivity x)

monoIsInjective :: ( IsMorphism f
                   , IsProof p
                   , Lhs p ~ MonoTest1 f
                   , Rhs p ~ MonoTest2 f
                   ) => f -> p ->
                        Domain (Source f) ->
                        Domain (Source f) ->
                        Proofs (Domain (Target f)) ->
                        Proofs (Domain (Source f))
monoIsInjective f m x x' p = proof m $
   MPoint f (setConst x) (setConst x') (const p) Proxy star

monoId :: IsObject x => x -> Proof (MonoTest1 (Id x)) (MonoTest2 (Id x))
monoId x = Proof $ SYMM (IDLEFT (MonoTest1 (Id x))) :>
                   MONOTEST (Id x) :>
                   IDLEFT (MonoTest2 (Id x))

monoComp :: ( IsMorphism f
            , IsMorphism g
            , IsProof p
            , Source f ~ Target g
            , Lhs p ~ MonoTest1 (f :. g)
            , Rhs p ~ MonoTest2 (f :. g)
            ) => f -> g -> p -> Proof (MonoTest1 g) (MonoTest2 g)
monoComp f g p = Proof $
    MONOAPPLY (f :. g) (MonoTest1 g) (MonoTest2 g) p $
    ASS f g (MonoTest1 g) :>
    (f :.| MONOTEST g) :>
    SYMM (ASS f g (MonoTest2 g))

monoT :: ( IsMorphism f
         , Source f ~ T
         ) => f -> Proof (MonoTest1 f) (MonoTest2 f)
monoT f = Proof $ TERMINAL (MonoTest1 f) :> SYMM (TERMINAL (MonoTest2 f))
