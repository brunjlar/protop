{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}

module Protop.Logic.Simple
    ( SCOPE(..)
    , SIG(..)
    , ENTITY(..)
    , sigE
    , showE
    , lftSIG
    , lftE
    , emptySC
    , consSC
    , objSIG
    , morSIG
    , prfSIG
    , lamSIG
    , varE
    , lamE
    , appE
    , scopeSIG
    , scopeE
    ) where

import Data.Typeable      (Typeable, eqT, (:~:)(..))
import Protop.Logic.Types

class Typeable ks => Simple (ks :: [Kind]) where

    lamS_ :: Simple' k => Sig    ks k -> SIG

    lam_  :: Simple' k => Entity ks k -> ENTITY

instance Simple '[] where

    lamS_ s = error $ "can't generalize signature with empty scope: " ++ show s

    lam_ e  = error $ "can't generalize entity with empty scope: "    ++ show e

instance (Simple ks, Simple' k') => Simple (k' ': ks) where

    lamS_ = SIG    . lamS

    lam_  = ENTITY . lam

class Typeable k => Simple' (k :: Kind) where

    app_ :: Typeable ks => Entity ks k -> ENTITY -> ENTITY

instance Simple' 'OBJ where

    app_ x _ = error $ "can't apply object " ++ show' x

instance Simple' 'MOR where

    app_ f _ = error $ "can't apply morphism " ++ show' f

instance Simple' 'PRF where

    app_ p _ = error $ "can't apply proof " ++ show' p

instance (Simple' k, Simple' k') => Simple' ('LAM k k') where

    app_ (e :: Entity ks ('LAM k k')) (ENTITY (f :: Entity ls l))
        = case (eqT :: Maybe (ks :~: ls), eqT :: Maybe (k :~: l)) of
            (Just Refl, Just Refl) -> ENTITY $ app e f
            (_        , _        ) ->
                error $ "can't apply " ++
                        show' e ++ " (" ++ show (scope e) ++ ") to " ++
                        show' f ++ " (" ++ show (scope f) ++ ")"

data SCOPE where

    SCOPE :: Simple ks => Scope ks -> SCOPE

data SIG where

    SIG :: (Simple ks , Simple' k) => Sig ks k -> SIG

data ENTITY where

    ENTITY :: (Simple ks, Simple' k) => Entity ks k -> ENTITY

instance Eq SCOPE where

    SCOPE (sc :: Scope ks) == SCOPE (sc' :: Scope ks')
        = case eqT :: Maybe (Scope ks :~: Scope ks') of
            Just Refl -> sc == sc'
            Nothing   -> False

instance Eq SIG where

    SIG (s :: Sig ks k) == SIG (t :: Sig ls l)
        = case eqT :: Maybe (Sig ks k :~: Sig ls l) of
            Just Refl -> s == t
            Nothing   -> False

instance Eq ENTITY where

    ENTITY (e :: Entity ks k) == ENTITY (f :: Entity ls l)
        = case eqT :: Maybe (Entity ks k :~: Entity ls l) of
            Just Refl -> e == f
            Nothing   -> False

instance Show SCOPE where

    show (SCOPE sc) = show sc

instance Show SIG where

    show (SIG s) = show s

instance Show ENTITY where

    show (ENTITY e) = show e

sigE :: ENTITY -> SIG
sigE (ENTITY e) = SIG $ sig e

showE :: ENTITY -> String
showE (ENTITY e) = show' e

lftSIG :: SIG -> SIG -> SIG
lftSIG (SIG (s :: Sig ks k))
       (SIG (t :: Sig ls l)) =
    case (eqT :: Maybe (ks :~: ls)) of
        Just Refl -> SIG $ lft s t
        Nothing   -> error $ "can't lift " ++ show t ++ " (" ++ show (scope t) ++
                             ") by " ++ show s ++ " (" ++ show (scope s) ++ ")"

lftE :: SIG -> ENTITY -> ENTITY
lftE (SIG    (s :: Sig    ks k))
     (ENTITY (e :: Entity ls l)) =
    case (eqT :: Maybe (ks :~: ls)) of
        Just Refl -> ENTITY $ lft s e
        Nothing   -> error  $ "can't lift " ++ show e ++ " (" ++ show (scope e) ++
                              ") by " ++ show s ++ " (" ++ show (scope s) ++ ")"



emptySC :: SCOPE
emptySC = SCOPE Empty

consSC :: SIG -> SCOPE
consSC (SIG s) = SCOPE $ Cons s

objSIG :: SCOPE -> SIG
objSIG (SCOPE sc) = SIG $ objS sc

morSIG :: ENTITY -> ENTITY -> SIG
morSIG (ENTITY (x :: Entity ks k))
       (ENTITY (y :: Entity ls l)) =
    case (eqT :: Maybe (k :~: 'OBJ), eqT :: Maybe (Entity ks k :~: Entity ls l)) of
        (Just Refl, Just Refl) -> SIG $ morS x y
        (_        , _        ) -> error $ "can't make a morphism signature from entities " ++
                                          show x ++ " (" ++ show (scope x) ++ ") and " ++
                                          show y ++ " (" ++ show (scope y) ++ ")"

prfSIG :: ENTITY -> ENTITY -> SIG
prfSIG (ENTITY (f :: Entity ks k))
       (ENTITY (g :: Entity ls l)) =
    case (eqT :: Maybe (k :~: 'MOR), eqT :: Maybe (Entity ks k :~: Entity ls l)) of
        (Just Refl, Just Refl) -> SIG $ prfS f g
        (_        , _        ) -> error $ "can't make a proof signature from entities " ++
                                          show f ++ " (" ++ show (scope f) ++ ") and " ++
                                          show g ++ " (" ++ show (scope g) ++ ")"

lamSIG :: SIG -> SIG
lamSIG (SIG s) = lamS_ s

varE :: SIG -> ENTITY
varE (SIG s) = ENTITY $ var s

lamE :: ENTITY -> ENTITY
lamE (ENTITY e) = lam_ e

appE :: ENTITY -> ENTITY -> ENTITY
appE (ENTITY e) = app_ e

scopeSIG :: SIG -> SCOPE
scopeSIG (SIG s) = SCOPE $ scope s

scopeE :: ENTITY -> SCOPE
scopeE (ENTITY e) = SCOPE $ scope e
