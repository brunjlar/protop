{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Protop.Core.Monos
    ( MonoTest(..)
    , MonoTest1(..)
    , MonoTest2(..)
    , MONOTEST(..)
    , MONOAPPLY(..)
    , setConst
    , CMONO
    , MonoProof
    , monoIsInjective
    , monoEq
    , monoId
    , monoComp
    , monoComp'
    , monoT
    , monoDiag
    ) where

import Data.Proxy                 (Proxy(..))
import Protop.Core.Compositions
import Protop.Core.Identities
import Protop.Core.Objects
import Protop.Core.Morphisms
import Protop.Core.Products
import Protop.Core.Proofs
import Protop.Core.Setoids
import Protop.Core.Symmetries
import Protop.Core.Terminal
import Protop.Core.Transitivities
import Protop.Utility

data MPoint :: * -> * where

    MPoint :: ( IsMorphism f
              , IsSetoid z
              ) => f ->
                   Functoid z (DSource f) ->
                   Functoid z (DSource f) ->
                   (z -> PTarget f) ->
                   Proxy z -> z -> MPoint f

data MProof :: * -> * where

    MProof :: ( IsMorphism f
              , IsSetoid z
              ) => f ->
                   Functoid z (DSource f) ->
                   Functoid z (DSource f) ->
                   (z -> PTarget f) ->
                   Proxy z -> Proofs z -> MProof f

instance IsMorphism f => IsSetoid (MPoint f) where

    type Proofs (MPoint f) = MProof f

    reflexivity (MPoint f t t' p r x)      =
        MProof f t t' p r $ reflexivity x
    symmetry _ (MProof f t t' p r px)      =
        MProof f t t' p r $ symmetry r px
    transitivity _ (MProof f t t' p  r px)
                   (MProof _ s s' p' _ qx) =
        case (eqT' t s, eqT' t' s', eqT' p p') of
           (Refl, Refl, Refl) ->
                MProof f t t' p r $ transitivity r px qx
    setLhs (MProof f t t' p r px) = MPoint f t t' p r $ setLhs px
    setRhs (MProof f t t' p r px) = MPoint f t t' p r $ setRhs px

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

type CMONOAPPLY f t t' p p' = ( CMONO f p
                              , IsMorphism t
                              , IsMorphism t'
                              , IsProof p'
                              , Source t ~ Source t'
                              , Target t ~ Target t'
                              , Target t ~ Source f
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

type CMONO f m = ( IsMorphism f
                 , IsProof m
                 , Lhs m ~ MonoTest1 f
                 , Rhs m ~ MonoTest2 f
                 )

type MonoProof f = Proof (MonoTest1 f) (MonoTest2 f)

setConst :: IsSetoid x => x -> Functoid Star x
setConst  x = Functoid (const x) (const $ reflexivity x)

monoIsInjective :: ( CMONO f p
                   ) => f -> p ->
                        DSource f ->
                        DSource f ->
                        PTarget f ->
                        PSource f
monoIsInjective f m x x' p = proof m $
   MPoint f (setConst x) (setConst x') (const p) Proxy star

monoEq :: ( CMONO f m
          , IsMorphism f'
          , IsProof p
          , Lhs p ~ f
          , Rhs p ~ f'
          ) => f -> m -> f' -> p -> MonoProof f'
monoEq f m f' p =
    let t  = MonoTest1 f'
        t' = MonoTest2 f'
    in  Proof $ MONOAPPLY f t t' m $
            (p :|. t) :>
            MONOTEST f' :>
            (SYMM p :|. t')

monoId :: IsObject x => x -> MonoProof (Id x)
monoId x = Proof $ SYMM (IDLEFT (MonoTest1 (Id x))) :>
                   MONOTEST (Id x) :>
                   IDLEFT (MonoTest2 (Id x))

monoComp :: ( IsMorphism f
            , IsMorphism g
            , Source f ~ Target g
            , CMONO (f :. g) p
            ) => f -> g -> p -> MonoProof g
monoComp f g p = Proof $
    MONOAPPLY (f :. g) (MonoTest1 g) (MonoTest2 g) p $
    ASS f g (MonoTest1 g) :>
    (f :.| MONOTEST g) :>
    SYMM (ASS f g (MonoTest2 g))

monoComp' :: ( CMONO f mf
             , CMONO g mg
             , Source f ~ Target g
             ) => f -> mf -> g -> mg -> MonoProof (f :. g)
monoComp' f mf g mg =
    let fg = f :. g
        t  = MonoTest1 fg
        t' = MonoTest2 fg
        p  = SYMM (ASS f g t) :> MONOTEST fg :> ASS f g t'
        q  = MONOAPPLY f (g :. t) (g :. t') mf p
    in  Proof $ MONOAPPLY g t t' mg q

monoT :: (IsMorphism f, Source f ~ T) => f -> MonoProof f
monoT f = Proof $ TERMINAL (MonoTest1 f) :> SYMM (TERMINAL (MonoTest2 f))

monoDiag :: IsObject x => x -> MonoProof (Diag x)
monoDiag x =
    let d  = diag x
        t  = MonoTest1 d
        t' = MonoTest2 d
        pr = Pr1 x x
    in  Proof $
            SYMM (IDLEFT t) :>
            (SYMM (PROD1 (Id x) (Id x)) :|. t) :>
            ASS pr d t :>
            (pr :.| MONOTEST d) :>
            SYMM (ASS pr d t') :>
            (PROD1 (Id x) (Id x) :|. t') :>
            IDLEFT t'
