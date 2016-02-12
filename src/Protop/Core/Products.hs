{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}

module Protop.Core.Products
    ( (:*)(..)
    , Pr1(..)
    , Pr2(..)
    , (:&&&)(..)
    , PROD1(..)
    , PROD2(..)
    , PROD(..)
    , Diag
    , diag
    ) where

import Data.Proxy               (Proxy(..))
import Protop.Core.Compositions
import Protop.Core.Identities
import Protop.Core.Morphisms
import Protop.Core.Objects
import Protop.Core.Proofs
import Protop.Core.Setoids

infixl 7 :*

type CProd a b = (IsObject a, IsObject b)

data (:*) :: * -> * -> * where
   (:*) :: CProd a b => a -> b -> a :* b

instance Show (a :* b) where

    show (x :* y) = "(" ++ show x ++ " * " ++ show y ++ ")"

instance CProd a b => IsObject (a :* b) where

    type Domain (a :* b) = (Domain a, Domain b)

    proxy _ = proxy Proxy :* proxy Proxy

data Pr1 :: * -> * -> * where
    Pr1 :: CProd a b => a -> b -> Pr1 a b

instance Show (Pr1 a b) where

    show (Pr1 x y) = "(pr1 " ++ show x ++ " " ++ show y ++ ")"

instance CProd a b => IsMorphism (Pr1 a b) where

    type Source (Pr1 a b) = a :* b
    type Target (Pr1 a b) = a
    onDomains _ = setPr1
    proxy' _ = Pr1 (proxy Proxy) (proxy Proxy)

data Pr2 :: * -> * -> * where
    Pr2 :: CProd a b => a -> b -> Pr2 a b

instance Show (Pr2 a b) where

    show (Pr2 x y) = "(pr2 " ++ show x ++ " " ++ show y ++ ")"

instance CProd a b => IsMorphism (Pr2 a b) where

    type Source (Pr2 a b) = a :* b
    type Target (Pr2 a b) = b
    onDomains _ = setPr2
    proxy' _ = Pr2 (proxy Proxy) (proxy Proxy)

type CProd' a b = (IsMorphism a, IsMorphism b, Source a ~ Source b)

infixl 7 :&&& 

data (:&&&) :: * -> * -> * where
    (:&&&) :: CProd' a b => a -> b -> a :&&& b

instance Show (a :&&& b) where

    show (a :&&& b) = "(" ++ show a ++ ", " ++ show b ++ ")"

instance CProd' a b => IsMorphism (a :&&& b) where

    type Source (a :&&& b) = Source b
    type Target (a :&&& b) = Target a :* Target b

    onDomains (f :&&& g) = setProd (onDomains f) (onDomains g)
    proxy' _ = proxy' Proxy :&&& proxy' Proxy

data PROD1 :: * -> * -> * where
    PROD1 :: CProd' a b => a -> b -> PROD1 a b

instance Show (PROD1 a b) where

    show (PROD1 a b) = "(PROD1 " ++ show a ++ " " ++ show b ++ ")"

instance CProd' a b => IsProof (PROD1 a b) where

    type Lhs (PROD1 a b) = Pr1 (Target a) (Target b) :. (a :&&& b)
    type Rhs (PROD1 a b) = a

    proof (PROD1 f _) x = reflexivity $ f .$ x
    proxy'' _           = PROD1 (proxy' Proxy) (proxy' Proxy)

data PROD2 :: * -> * -> * where
    PROD2 :: CProd' a b => a -> b -> PROD2 a b

instance Show (PROD2 a b) where

    show (PROD2 a b) = "(PROD2 " ++ show a ++ " " ++ show b ++ ")"

instance CProd' a b => IsProof (PROD2 a b) where

    type Lhs (PROD2 a b) = Pr2 (Target a) (Target b) :. (a :&&& b)
    type Rhs (PROD2 a b) = b

    proof (PROD2 _ g) x = reflexivity $ g .$ x
    proxy'' _           = PROD2 (proxy' Proxy) (proxy' Proxy)

type CPROD a b c = ( IsMorphism a
                   , IsProof b
                   , IsProof c
                   , Target a ~ (PTarget b :* PTarget c)
                   , Lhs b ~ (Pr1 (PTarget b) (PTarget c) :. a)
                   , Lhs c ~ (Pr2 (PTarget b) (PTarget c) :. a)
                   )

data PROD :: * -> * -> * -> * where
    PROD :: CPROD a b c => a -> b -> c -> PROD a b c

instance Show (PROD a b c) where

    show (PROD f p q) = "(PROD " ++ show f ++ " " ++ show p ++ " " ++ show q ++ ")"
    
instance CPROD a b c => IsProof (PROD a b c) where

    type Lhs (PROD a b c) = a
    type Rhs (PROD a b c) = Rhs b :&&& Rhs c

    proof (PROD _ p q) x = (proof p x, proof q x)
    proxy'' _ = PROD (proxy' Proxy) (proxy'' Proxy) (proxy'' Proxy)

type Diag x = Id x :&&& Id x
diag :: IsObject x => x -> Diag x
diag _ = proxy' Proxy
