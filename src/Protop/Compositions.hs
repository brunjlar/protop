{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}

module Protop.Compositions
    ( (:.)(..)
    , (:.|)(..)
    , (:|.)(..)
    , ASS(..)
    ) where

import Data.Proxy       (Proxy(..))
import Protop.Morphisms
import Protop.Proofs
import Protop.Setoids

type CComp a b = (IsMorphism a, IsMorphism b, Source a ~ Target b)

infixr 9 :.

data (:.) :: * -> * -> * where
    (:.) :: CComp a b => a -> b -> a :. b

instance Show (a :. b) where

    show (f :. g) = "(" ++ show f ++ " . " ++ show g ++ ")"

instance CComp a b => IsMorphism (a :. b) where

    type Source (a :. b) = Source b
    type Target (a :. b) = Target a

    onDomains (f :. g) = setComp (onDomains f) (onDomains g)
    proxy' _           = proxy' Proxy :. proxy' Proxy

type CCOMPLEFT a b = (IsMorphism a, IsProof b, Source a ~ PTarget b)

infix :.|

data (:.|) :: * -> * -> * where
    (:.|) :: CCOMPLEFT a b => a -> b -> a :.| b

instance Show (a :.| b) where

    show (a :.| b) = "(" ++ show a ++ " . " ++ show b ++ ")"

instance CCOMPLEFT a b => IsProof (a :.| b) where

    type Lhs (a :.| b) = a :. Lhs b
    type Rhs (a :.| b) = a :. Rhs b

    proof (f :.| p) x = let Functoid _ g = onDomains f in g $ proof p x
    proxy'' _         = proxy' Proxy :.| proxy'' Proxy

type CCOMPRIGHT a b = (IsProof a, IsMorphism b, PSource a ~ Target b)

infix :|.

data (:|.) :: * -> * -> * where
    (:|.) :: CCOMPRIGHT a b => a -> b -> a :|. b

instance Show (a :|. b) where

    show (a :|. b) = "(" ++ show a ++ " . " ++ show b ++ ")"

instance CCOMPRIGHT a b => IsProof (a :|. b) where

    type Lhs (a :|. b) = Lhs a :. b
    type Rhs (a :|. b) = Rhs a :. b

    proof (p :|. f) x = proof p $ f .$ x
    proxy'' _ = proxy'' Proxy :|. proxy' Proxy

type CASS a b c = (IsMorphism a, IsMorphism b, IsMorphism c, Source a ~ Target b, Source b ~ Target c)

data ASS :: * -> * -> * -> * where
    ASS :: CASS a b c => a -> b -> c -> ASS a b c

instance Show (ASS a b c) where

    show (ASS a b c) = "(ASS " ++ show a ++ " " ++ show b ++ " " ++ show c ++ ")"

instance CASS a b c => IsProof (ASS a b c) where

    type Lhs (ASS a b c) = (a :. b) :. c
    type Rhs (ASS a b c) = a :. b :. c

    proof (ASS f g h) x = reflexivity $ f .$ g .$ h .$ x 
    proxy'' _           = ASS (proxy' Proxy) (proxy' Proxy) (proxy' Proxy)
