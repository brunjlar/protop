{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

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
    , varE
    ) where

import Data.Typeable      (Typeable, eqT, (:~:)(..))
import Protop.Logic.Types

data SCOPE where

    SCOPE :: Typeable ks => Scope ks -> SCOPE

data SIG where

    SIG :: (Typeable ks, Typeable k) => Sig ks k -> SIG

data ENTITY where

    ENTITY :: (Typeable ks, Typeable k) => Entity ks k -> ENTITY

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

varE :: SIG -> ENTITY
varE (SIG s) = ENTITY $ var s
