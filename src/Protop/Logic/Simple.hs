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
    , sgmSIG
    , varE
    , lamE
    , appE
    , sgmE
    , scopeSIG
    , scopeE
    ) where

import Data.Typeable      (Typeable, eqT, (:~:)(..))
import Protop.Logic.Types

class Typeable ks => Simple (ks :: [Kind]) where

    lamS_ :: Simple' k => Sig    k ks -> SIG

    lam_  :: Simple' k => Entity k ks -> ENTITY

    sgmS_ :: Simple' k => Sig    k ks -> SIG

    sgm_  :: (Simple' k, Simple' k') => Sig ('SGM k k') ks -> Entity k ks -> Entity k' ks -> ENTITY

instance Simple '[] where

    lamS_ s = error $ "can't generalize signature with empty scope: " ++ show s

    lam_ e  = error $ "can't generalize entity with empty scope: "    ++ show e

    sgmS_ s = error $ "can't make sigma signature with empty scope: " ++ show s

    sgm_ s e f = ENTITY $ sgm s e f

instance (Simple ks, Simple' k') => Simple (k' ': ks) where

    lamS_      = SIG    . lamS

    lam_       = ENTITY . lam

    sgmS_      = SIG    . sgmS

    sgm_ s e f = ENTITY $ sgm s e f

class Typeable k => Simple' (k :: Kind) where

    app_ :: Typeable ks => Entity k ks -> ENTITY -> ENTITY

instance Simple' 'OBJ where

    app_ x _ = error $ "can't apply object " ++ show' x

instance Simple' 'MOR where

    app_ f _ = error $ "can't apply morphism " ++ show' f

instance Simple' 'PRF where

    app_ p _ = error $ "can't apply proof " ++ show' p

instance (Simple' k, Simple' k') => Simple' ('LAM k k') where

    app_ (e :: Entity ('LAM k k') ks) (ENTITY (f :: Entity l ls))
        = case (eqT :: Maybe (ks :~: ls), eqT :: Maybe (k :~: l)) of
            (Just Refl, Just Refl) -> ENTITY $ app e f
            (_        , _        ) ->
                error $ "can't apply " ++
                        show' e ++ " (" ++ show (scope e) ++ ") to " ++
                        show' f ++ " (" ++ show (scope f) ++ ")"

instance (Simple' k, Simple' k') => Simple' ('SGM k k') where

    app_ e _ = error $ "can't apply sigma entity " ++ show' e

data SCOPE where

    SCOPE :: Simple ks => Scope ks -> SCOPE

data SIG where

    SIG :: (Simple ks , Simple' k) => Sig k ks -> SIG

data ENTITY where

    ENTITY :: (Simple ks, Simple' k) => Entity k ks -> ENTITY

instance Eq SCOPE where

    SCOPE (sc :: Scope ks) == SCOPE (sc' :: Scope ks')
        = case eqT :: Maybe (Scope ks :~: Scope ks') of
            Just Refl -> sc == sc'
            Nothing   -> False

instance Eq SIG where

    SIG (s :: Sig k ks) == SIG (t :: Sig l ls)
        = case eqT :: Maybe (Sig k ks :~: Sig l ls) of
            Just Refl -> s == t
            Nothing   -> False

instance Eq ENTITY where

    ENTITY (e :: Entity k ks) == ENTITY (f :: Entity l ls)
        = case eqT :: Maybe (Entity k ks :~: Entity l ls) of
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
lftSIG (SIG (s :: Sig k ks))
       (SIG (t :: Sig l ls)) =
    case (eqT :: Maybe (ks :~: ls)) of
        Just Refl -> SIG $ lft s t
        Nothing   -> error $ "can't lift " ++ show t ++ " (" ++ show (scope t) ++
                             ") by " ++ show s ++ " (" ++ show (scope s) ++ ")"

lftE :: SIG -> ENTITY -> ENTITY
lftE (SIG    (s :: Sig    k ks))
     (ENTITY (e :: Entity l ls)) =
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
morSIG (ENTITY (x :: Entity k ks))
       (ENTITY (y :: Entity l ls)) =
    case (eqT :: Maybe (k :~: 'OBJ), eqT :: Maybe (Entity k ks :~: Entity l ls)) of
        (Just Refl, Just Refl) -> SIG $ morS x y
        (_        , _        ) -> error $ "can't make a morphism signature from entities " ++
                                          show x ++ " (" ++ show (scope x) ++ ") and " ++
                                          show y ++ " (" ++ show (scope y) ++ ")"

prfSIG :: ENTITY -> ENTITY -> SIG
prfSIG (ENTITY (f :: Entity k ks))
       (ENTITY (g :: Entity l ls)) =
    case (eqT :: Maybe (k :~: 'MOR), eqT :: Maybe (Entity k ks :~: Entity l ls)) of
        (Just Refl, Just Refl) -> SIG $ prfS f g
        (_        , _        ) -> error $ "can't make a proof signature from entities " ++
                                          show f ++ " (" ++ show (scope f) ++ ") and " ++
                                          show g ++ " (" ++ show (scope g) ++ ")"

lamSIG :: SIG -> SIG
lamSIG (SIG s) = lamS_ s

sgmSIG :: SIG -> SIG
sgmSIG (SIG s) = sgmS_ s

varE :: SIG -> ENTITY
varE (SIG s) = ENTITY $ var s

lamE :: ENTITY -> ENTITY
lamE (ENTITY e) = lam_ e

appE :: ENTITY -> ENTITY -> ENTITY
appE (ENTITY e) = app_ e

sgmE :: SIG -> ENTITY -> ENTITY -> ENTITY
sgmE (SIG    (s :: Sig    k ks))
     (ENTITY (e :: Entity l ls))
     (ENTITY (f :: Entity m ms)) =
    case (eqT :: Maybe (k :~: 'SGM l m), eqT :: Maybe (ks :~: ls), eqT :: Maybe (ls :~: ms)) of
        (Just Refl, Just Refl, Just Refl) -> sgm_ s e f
        (_        , _        , _        ) -> error $ "can't make a sigma entity from entities " ++
                                                     show e ++ " (" ++ show (scope e) ++ ") and " ++
                                                     show f ++ " (" ++ show (scope f) ++ ") for signature " ++
                                                     show s ++ " (" ++ show (scope s) ++ ")"

scopeSIG :: SIG -> SCOPE
scopeSIG (SIG s) = SCOPE $ scope s

scopeE :: ENTITY -> SCOPE
scopeE (ENTITY e) = SCOPE $ scope e
