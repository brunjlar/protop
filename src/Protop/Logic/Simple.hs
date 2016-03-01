{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Protop.Logic.Simple
    ( Scope(..)
    , Sig(..)
    , Entity(..)
    , Liftable(..)
    , HasScope(..)
    , lft'
    , headTail
    , sig
    , show'
    , empty
    , cons
    , objS
    , morS
    , prfS
    , lamS
    , sgmS
    , var
    , lam
    , app
    , sgm
    ) where

import           Data.Typeable      (Typeable, eqT, (:~:)(..))
import qualified Protop.Logic.Types as T

data Scope where

    Scope :: Simple ks => T.Scope ks -> Scope

data Sig where

    Sig :: (Simple ks , Simple' k) => T.Sig k ks -> Sig

data Entity where

    Entity :: (Simple ks, Simple' k) => T.Entity k ks -> Entity

instance Eq Scope where

    Scope (sc :: T.Scope ks) == Scope (sc' :: T.Scope ks')
        = case eqT :: Maybe (ks :~: ks') of
            Just Refl -> sc == sc'
            Nothing   -> False

instance Eq Sig where

    Sig (s :: T.Sig k ks) == Sig (t :: T.Sig l ls)
        = case eqT :: Maybe (T.Sig k ks :~: T.Sig l ls) of
            Just Refl -> s == t
            Nothing   -> False

instance Eq Entity where

    Entity (e :: T.Entity k ks) == Entity (f :: T.Entity l ls)
        = case eqT :: Maybe (T.Entity k ks :~: T.Entity l ls) of
            Just Refl -> e == f
            Nothing   -> False

instance Show Scope where

    show (Scope sc) = show sc

instance Show Sig where

    show (Sig s) = show s

instance Show Entity where

    show (Entity e) = show e

headTail :: Scope -> Maybe (Sig, Scope)
headTail (Scope sc) = case sc of
                            T.Empty  -> Nothing
                            T.Cons _ -> Just $ headTail_ sc

sig :: Entity -> Sig
sig (Entity e) = Sig $ T.sig e

show' :: Entity -> String
show' (Entity e) = T.show' e

class Liftable a where

    lft :: Sig -> a -> a

instance Liftable Sig where

    lft s@(Sig (s' :: T.Sig k ks))
        t@(Sig (t' :: T.Sig l ls)) =
            case (eqT :: Maybe (ks :~: ls)) of
              Just Refl -> Sig $ T.lft s' t'
              Nothing   -> error $ "can't lift " ++ showSC t ++ " by " ++ showSC s

instance Liftable Entity where

    lft s@(Sig    (s' :: T.Sig    k ks))
        e@(Entity (e' :: T.Entity l ls)) =
            case (eqT :: Maybe (ks :~: ls)) of
              Just Refl -> Entity $ T.lft s' e'
              Nothing   -> error  $ "can't lift " ++ showSC e ++ " by " ++ showSC s

class HasScope a where

    scope :: a -> Scope

instance HasScope Scope where

    scope = id

instance HasScope Sig where

    scope (Sig s) = Scope $ T.scope s

instance HasScope Entity where

    scope (Entity e) = Scope $ T.scope e

lft' :: (Liftable a, HasScope a, Show a) => Scope -> a -> a
lft' sc x
    | scope x == sc = x
    | otherwise     =
        case headTail sc of
          Nothing        -> error $ "can't lift " ++ showSC x ++ " into scope " ++ show sc
          Just (s', sc') -> lft s' $ lft' sc' x

empty :: Scope
empty = Scope T.Empty

cons :: Sig -> Scope
cons (Sig s) = Scope $ T.Cons s

objS :: Scope -> Sig
objS (Scope sc) = Sig $ T.objS sc

morS :: Entity -> Entity -> Sig
morS x@(Entity (x' :: T.Entity k ks))
     y@(Entity (y' :: T.Entity l ls)) =
         case (eqT :: Maybe (k :~: 'T.OBJ), eqT :: Maybe (T.Entity k ks :~: T.Entity l ls)) of
           (Just Refl, Just Refl) -> Sig $ T.morS x' y'
           (_        , _        ) -> error $ "can't make a morphism signature from entities " ++
                                             showSC x ++ " and " ++ showSC y

prfS :: Entity -> Entity -> Sig
prfS f@(Entity (f' :: T.Entity k ks))
     g@(Entity (g' :: T.Entity l ls)) =
         case (eqT :: Maybe (k :~: 'T.MOR), eqT :: Maybe (T.Entity k ks :~: T.Entity l ls)) of
           (Just Refl, Just Refl) -> Sig $ T.prfS f' g'
           (_        , _        ) -> error $ "can't make a proof signature from entities " ++
                                             showSC f ++ " and " ++ showSC g


lamS :: Sig -> Sig
lamS (Sig s) = lamS_ s

sgmS :: Sig -> Sig
sgmS (Sig s) = sgmS_ s

var :: Sig -> Entity
var (Sig s) = Entity $ T.var s

lam :: Entity -> Entity
lam (Entity e) = lam_ e

app :: Entity -> Entity -> Entity
app (Entity e) = app_ e

sgm :: Sig -> Entity -> Entity -> Entity
sgm s@(Sig    (s' :: T.Sig    k ks))
    e@(Entity (e' :: T.Entity l ls))
    f@(Entity (f' :: T.Entity m ms)) =
        case (eqT :: Maybe (k :~: 'T.SGM l m), eqT :: Maybe (ks :~: ls), eqT :: Maybe (ls :~: ms)) of
          (Just Refl, Just Refl, Just Refl) -> sgm_ s' e' f'
          (_        , _        , _        ) -> error $ "can't make a sigma entity from entities " ++
                                                       showSC e ++ " and " ++ showSC f ++ " for " ++ showSC s

class Typeable ks => Simple (ks :: [T.Kind]) where

    lamS_     :: Simple' k => T.Sig    k ks -> Sig

    lam_      :: Simple' k => T.Entity k ks -> Entity

    sgmS_     :: Simple' k => T.Sig    k ks -> Sig

    sgm_      :: (Simple' k, Simple' k') => T.Sig ('T.SGM k k') ks -> T.Entity k ks -> T.Entity k' ks -> Entity

    headTail_ :: T.Scope ks -> (Sig, Scope)

instance Simple '[] where

    lamS_ s = error $ "can't generalize signature with empty scope: " ++ show s

    lam_ e  = error $ "can't generalize entity with empty scope: "    ++ show e

    sgmS_ s = error $ "can't make sigma signature with empty scope: " ++ show s

    sgm_ s e f = Entity $ T.sgm s e f

    headTail_ _ = error "can't get head and tail of empty scope"

instance (Simple ks, Simple' k') => Simple (k' ': ks) where

    lamS_        = Sig    . T.lamS

    lam_         = Entity . T.lam

    sgmS_        = Sig    . T.sgmS

    sgm_ s e f   = Entity $ T.sgm s e f

    headTail_ sc = (Sig $ T.headSC sc, Scope $ T.tailSC sc)

class Typeable k => Simple' (k :: T.Kind) where

    app_ :: Typeable ks => T.Entity k ks -> Entity -> Entity

instance Simple' 'T.OBJ where

    app_ x _ = error $ "can't apply object " ++ T.show' x

instance Simple' 'T.MOR where

    app_ f _ = error $ "can't apply morphism " ++ T.show' f

instance Simple' 'T.PRF where

    app_ p _ = error $ "can't apply proof " ++ T.show' p

instance (Simple' k, Simple' k') => Simple' ('T.LAM k k') where

    app_ (e :: T.Entity ('T.LAM k k') ks) (Entity (f :: T.Entity l ls))
        = case (eqT :: Maybe (ks :~: ls), eqT :: Maybe (k :~: l)) of
            (Just Refl, Just Refl) -> Entity $ T.app e f
            (_        , _        ) ->
                error $ "can't apply " ++
                        T.show' e ++ " (" ++ show (T.scope e) ++ ") to " ++
                        T.show' f ++ " (" ++ show (T.scope f) ++ ")"

instance (Simple' k, Simple' k') => Simple' ('T.SGM k k') where

    app_ e _ = error $ "can't apply sigma entity " ++ T.show' e

showSC :: (Show a, HasScope a) => a -> String
showSC x = show x ++ " (" ++ show (scope x) ++ ")"
