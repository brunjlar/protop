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

import           Data.Typeable        (Typeable, eqT, (:~:)(..))
import qualified Protop.Logic.Indexed as I

data Scope where

    Scope :: Simple ks => I.Scope ks -> Scope

data Sig where

    Sig :: (Simple ks , Simple' k) => I.Sig k ks -> Sig

data Entity where

    Entity :: (Simple ks, Simple' k) => I.Entity k ks -> Entity

instance Eq Scope where

    Scope (sc :: I.Scope ks) == Scope (sc' :: I.Scope ks')
        = case eqT :: Maybe (ks :~: ks') of
            Just Refl -> sc == sc'
            Nothing   -> False

instance Eq Sig where

    Sig (s :: I.Sig k ks) == Sig (t :: I.Sig l ls)
        = case eqT :: Maybe (I.Sig k ks :~: I.Sig l ls) of
            Just Refl -> s == t
            Nothing   -> False

instance Eq Entity where

    Entity (e :: I.Entity k ks) == Entity (f :: I.Entity l ls)
        = case eqT :: Maybe (I.Entity k ks :~: I.Entity l ls) of
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
                            I.Empty  -> Nothing
                            I.Cons _ -> Just $ headTail_ sc

sig :: Entity -> Sig
sig (Entity e) = Sig $ I.sig e

show' :: Entity -> String
show' (Entity e) = I.show' e

class Liftable a where

    lft :: Sig -> a -> a

instance Liftable Sig where

    lft s@(Sig (s' :: I.Sig k ks))
        t@(Sig (t' :: I.Sig l ls)) =
            case (eqT :: Maybe (ks :~: ls)) of
              Just Refl -> Sig $ I.lft s' t'
              Nothing   -> error $ "can't lift " ++ showSC t ++ " by " ++ showSC s

instance Liftable Entity where

    lft s@(Sig    (s' :: I.Sig    k ks))
        e@(Entity (e' :: I.Entity l ls)) =
            case (eqT :: Maybe (ks :~: ls)) of
              Just Refl -> Entity $ I.lft s' e'
              Nothing   -> error  $ "can't lift " ++ showSC e ++ " by " ++ showSC s

class HasScope a where

    scope :: a -> Scope

instance HasScope Scope where

    scope = id

instance HasScope Sig where

    scope (Sig s) = Scope $ I.scope s

instance HasScope Entity where

    scope (Entity e) = Scope $ I.scope e

lft' :: (Liftable a, HasScope a, Show a) => Scope -> a -> a
lft' sc x
    | scope x == sc = x
    | otherwise     =
        case headTail sc of
          Nothing        -> error $ "can't lift " ++ showSC x ++ " into scope " ++ show sc
          Just (s', sc') -> lft s' $ lft' sc' x

empty :: Scope
empty = Scope I.Empty

cons :: Sig -> Scope
cons (Sig s) = Scope $ I.Cons s

objS :: Scope -> Sig
objS (Scope sc) = Sig $ I.objS sc

morS :: Entity -> Entity -> Sig
morS x@(Entity (x' :: I.Entity k ks))
     y@(Entity (y' :: I.Entity l ls)) =
         case (eqT :: Maybe (k :~: 'I.OBJ), eqT :: Maybe (I.Entity k ks :~: I.Entity l ls)) of
           (Just Refl, Just Refl) -> Sig $ I.morS x' y'
           (_        , _        ) -> error $ "can't make a morphism signature from entities " ++
                                             showSC x ++ " and " ++ showSC y

prfS :: Entity -> Entity -> Sig
prfS f@(Entity (f' :: I.Entity k ks))
     g@(Entity (g' :: I.Entity l ls)) =
         case (eqT :: Maybe (k :~: 'I.MOR), eqT :: Maybe (I.Entity k ks :~: I.Entity l ls)) of
           (Just Refl, Just Refl) -> Sig $ I.prfS f' g'
           (_        , _        ) -> error $ "can't make a proof signature from entities " ++
                                             showSC f ++ " and " ++ showSC g


lamS :: Sig -> Sig
lamS (Sig s) = lamS_ s

sgmS :: Sig -> Sig
sgmS (Sig s) = sgmS_ s

var :: Sig -> Entity
var (Sig s) = Entity $ I.var s

lam :: Entity -> Entity
lam (Entity e) = lam_ e

app :: Entity -> Entity -> Entity
app (Entity e) = app_ e

sgm :: Sig -> Entity -> Entity -> Entity
sgm s@(Sig    (s' :: I.Sig    k ks))
    e@(Entity (e' :: I.Entity l ls))
    f@(Entity (f' :: I.Entity m ms)) =
        case (eqT :: Maybe (k :~: 'I.SGM l m), eqT :: Maybe (ks :~: ls), eqT :: Maybe (ls :~: ms)) of
          (Just Refl, Just Refl, Just Refl) -> sgm_ s' e' f'
          (_        , _        , _        ) -> error $ "can't make a sigma entity from entities " ++
                                                       showSC e ++ " and " ++ showSC f ++ " for " ++ showSC s

class Typeable ks => Simple (ks :: [I.Kind]) where

    lamS_     :: Simple' k => I.Sig    k ks -> Sig

    lam_      :: Simple' k => I.Entity k ks -> Entity

    sgmS_     :: Simple' k => I.Sig    k ks -> Sig

    sgm_      :: (Simple' k, Simple' k') => I.Sig ('I.SGM k k') ks -> I.Entity k ks -> I.Entity k' ks -> Entity

    headTail_ :: I.Scope ks -> (Sig, Scope)

instance Simple '[] where

    lamS_ s = error $ "can't generalize signature with empty scope: " ++ show s

    lam_ e  = error $ "can't generalize entity with empty scope: "    ++ show e

    sgmS_ s = error $ "can't make sigma signature with empty scope: " ++ show s

    sgm_ s e f = Entity $ I.sgm s e f

    headTail_ _ = error "can't get head and tail of empty scope"

instance (Simple ks, Simple' k') => Simple (k' ': ks) where

    lamS_        = Sig    . I.lamS

    lam_         = Entity . I.lam

    sgmS_        = Sig    . I.sgmS

    sgm_ s e f   = Entity $ I.sgm s e f

    headTail_ sc = (Sig $ I.headSC sc, Scope $ I.tailSC sc)

class Typeable k => Simple' (k :: I.Kind) where

    app_ :: Typeable ks => I.Entity k ks -> Entity -> Entity

instance Simple' 'I.OBJ where

    app_ x _ = error $ "can't apply object " ++ I.show' x

instance Simple' 'I.MOR where

    app_ f _ = error $ "can't apply morphism " ++ I.show' f

instance Simple' 'I.PRF where

    app_ p _ = error $ "can't apply proof " ++ I.show' p

instance (Simple' k, Simple' k') => Simple' ('I.LAM k k') where

    app_ (e :: I.Entity ('I.LAM k k') ks) (Entity (f :: I.Entity l ls))
        = case (eqT :: Maybe (ks :~: ls), eqT :: Maybe (k :~: l)) of
            (Just Refl, Just Refl) -> Entity $ I.app e f
            (_        , _        ) ->
                error $ "can't apply " ++
                        I.show' e ++ " (" ++ show (I.scope e) ++ ") to " ++
                        I.show' f ++ " (" ++ show (I.scope f) ++ ")"

instance (Simple' k, Simple' k') => Simple' ('I.SGM k k') where

    app_ e _ = error $ "can't apply sigma entity " ++ I.show' e

showSC :: (Show a, HasScope a) => a -> String
showSC x = show x ++ " (" ++ show (scope x) ++ ")"
