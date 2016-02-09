{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}

module Protop.Omega
    ( OPoint(..)
    , OProof(..)
    , O(..)
    , True'
    , Sub(..)
    , SUB(..)
    , Omega(..)
    ) where

import Data.Proxy          (Proxy(..))
import Data.Typeable       (Typeable, (:~:)(..), eqT, typeRep)
import Protop.Compositions
import Protop.Identities
import Protop.Monos
import Protop.Morphisms
import Protop.Objects
import Protop.Proofs
import Protop.Setoids
import Protop.Terminal

data OPoint :: * where

    OPoint :: IsMorphism f => f -> Domain (Target f) ->
              Proofs (Domain (Target f)) -> OPoint

data OProof :: * where

    OProof :: ( IsMorphism f
              , IsMorphism g
              ) => f -> g -> 
                   (Domain (Source f) -> Domain (Source g)) ->
                   (Domain (Source g) -> Domain (Source f)) ->
                   Proofs (Domain (Target f)) ->
                   Proofs (Domain (Target g)) ->
                   OProof

instance IsSetoid OPoint where

    type Proofs OPoint = OProof

    reflexivity (OPoint f _ p) = OProof f f id id p p
    symmetry _ (OProof f g i j p q) = OProof g f j i q p
    transitivity _ (OProof f  g i  j  p _)
                   (OProof g' h i' j' _ r) =
        case eqT' g g' of Refl -> OProof f h (i' . i) (j . j') p r

data O = O

instance Show O where

    show O = "O"

instance IsObject O where

    type Domain O = OPoint

    proxy _ = O

data True' = True'

instance Show True' where

    show True' = "true"

instance IsMorphism True' where

    type Source True' = T
    type Target True' = O

    onDomains _ = Functoid (const x) (const px) where
        x  = OPoint (Id T) star star
        px = OProof (Id T) (Id T) id id star star

    proxy' _ = True'

type CSub f p = ( IsMorphism f
                , IsProof p
                , Lhs p ~ MonoTest1 f
                , Rhs p ~ MonoTest2 f
                )

data Sub :: * -> * -> * where
   
   Sub :: CSub f p => f -> p -> Sub f p

instance Show (Sub f p) where

    show (Sub f _) = "(sub " ++ show f ++ ")"

instance CSub f p => IsMorphism (Sub f p) where

    type Source (Sub f p) = Target f
    type Target (Sub f p) = O

    onDomains (Sub f _) = Functoid s s' where
        s  x  = OPoint f x (reflexivity x)
        s' px = OProof f f id id px
                (symmetry (Proxy :: Proxy (Domain (Target f))) px)

    proxy' _ = Sub (proxy' Proxy) (proxy'' Proxy)

data SUB :: * -> * -> * where
   
   SUB :: CSub f p => f -> p -> SUB f p

instance Show (SUB f p) where

    show (SUB f _) = "(SUB " ++ show f ++ ")"

instance CSub f p => IsProof (SUB f p) where

    type Lhs (SUB f p) = Sub f p :. f
    type Rhs (SUB f p) = True' :. Terminal (Source f)
  
    proof (SUB f _) x = OProof f (Id T) (const star) (const x) (reflexivity $ f .$ x) star
    proxy'' _         = SUB (proxy' Proxy) (proxy'' Proxy)

type COmega f p g q = ( CSub f p
                      , IsMorphism g
                      , IsProof q
                      , Target g ~ Target f
                      , Lhs q ~ (Sub f p :. g)
                      , Rhs q ~ (True' :. Terminal (Source g))
                      )

data Omega :: * -> * -> * -> * -> * where

    Omega :: COmega f p g q => f -> p -> g -> q -> Omega f p g q

instance Show (Omega f p g q) where

    show (Omega f _ g _) = "(omega " ++ show f ++ " " ++ show g ++ ")"

apply' :: forall a b a' b'. ( Typeable a
                                 , Typeable a'
                                 , Typeable b
                                 , Typeable b'
                                 ) => (a -> b) -> a' -> b'
apply' f x =
    let pa  = Proxy :: Proxy a
        pa' = Proxy :: Proxy a'
        pb  = Proxy :: Proxy b
        pb' = Proxy :: Proxy b'
    in case (eqT :: Maybe (a :~: a')) of
        Just Refl ->
            case (eqT :: Maybe (b :~: b')) of
                Just Refl -> f x
                Nothing   -> error $ "incompatible types " ++
                                     show (typeRep pb) ++ " and " ++
                                     show (typeRep pb')
        Nothing   -> error $ "incompatible type " ++
                             show (typeRep pa) ++ " and " ++
                             show (typeRep pa')

instance COmega f p g q => IsMorphism (Omega f p g q) where

    type Source (Omega f p g q) = Source g
    type Target (Omega f p g q) = Source f

    onDomains (Omega f p g q) = Functoid t t' where
        t   x = case proof q x of OProof _ _ _ j _ _ -> j `apply'` star
        t' px = undefined

    proxy' _ = Omega (proxy' Proxy)
                     (proxy'' Proxy)
                     (proxy' Proxy)
                     (proxy'' Proxy)
