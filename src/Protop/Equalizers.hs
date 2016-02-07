{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Protop.Equalizers
    ( (:==)(..)
    , Inj(..)
    , INJ(..)
    , Eql(..)
    , MONO(..)
    , monoInj
    ) where

import Data.Proxy            (Proxy(..))
import Protop.Compositions
import Protop.Monos
import Protop.Morphisms
import Protop.Objects
import Protop.Proofs
import Protop.Setoids

type CEql f g = ( IsMorphism f
                , IsMorphism g
                , Source f ~ Source g
                , Target f ~ Target g
                )

infix :==

data (:==) :: * -> * -> * where
    (:==) :: CEql f g => f -> g -> f :== g

instance (Show (f :== g)) where

    show (f :== g) = "(" ++ show f ++ " == " ++ show g ++ ")"

instance CEql f g => IsObject (f :== g) where

    type Domain (f :== g) = SetEql (Domain (Source f)) (Domain (Target f))

    proxy _ = proxy' Proxy :== proxy' Proxy
    
data Inj :: * -> * -> * where
    Inj :: CEql f g => f -> g -> Inj f g

instance (Show (Inj f g)) where

    show (Inj f g) = "(Inj " ++ show f ++ " " ++ show g ++ ")"

instance CEql f g => IsMorphism (Inj f g) where

    type Source (Inj f g) = f :== g
    type Target (Inj f g) = Source f

    onDomains _ = setInj
    proxy' _    = Inj (proxy' Proxy) (proxy' Proxy)

data INJ :: * -> * -> * where
    INJ :: CEql f g => f -> g -> INJ f g

instance (Show (INJ f g)) where

    show (INJ f g) = "(INJ " ++ show f ++ " " ++ show g ++ ")"

instance (CEql f g) => IsProof (INJ f g) where

    type Lhs (INJ f g) = f :. Inj f g
    type Rhs (INJ f g) = g :. Inj f g

    proof _ (SetEql _ px) = px
    proxy'' _             = INJ (proxy' Proxy) (proxy' Proxy)

type CEql' f g h p = ( CEql f g
                     , IsMorphism h
                     , IsProof p
                     , Target h ~ Source f
                     , Lhs p ~ (f :. h)
                     , Rhs p ~ (g :. h)
                     )

data Eql :: * -> * -> * -> * -> * where
    Eql :: CEql' f g h p => f -> g -> h -> p -> Eql f g h p

instance Show (Eql f g h p) where

    show (Eql f g h _) =
        "(Eql " ++ show f ++ " " ++ show g ++ " " ++ show h ++ ")"

instance CEql' f g h p => IsMorphism (Eql f g h p) where

    type Source (Eql f g h p) = Source h
    type Target (Eql f g h p) = f :== g

    onDomains (Eql _ _ h p) = Functoid h' h'' where
        h' z = SetEql (h .$ z) $ proof p z
        h''  = onProofs (onDomains h)
    proxy' _ = Eql (proxy' Proxy)
                   (proxy' Proxy)
                   (proxy' Proxy)
                   (proxy'' Proxy)

type CMONO f g t t' p = ( CEql f g
                        , IsMorphism t
                        , IsMorphism t'
                        , IsProof p
                        , Source t ~ Source t'
                        , Target t ~ Target t'
                        , Target t ~ (f :== g)
                        , Lhs p ~ (Inj f g :. t)
                        , Rhs p ~ (Inj f g :. t')
                        )

data MONO :: * -> * -> * -> * -> * -> * where
    MONO :: CMONO f g t t' p => f -> g -> t -> t' -> p -> MONO f g t t' p

instance Show (MONO f g t t' p) where
    show (MONO f g t t' p) =
        "(MONO " ++ show f ++ " " ++ show g ++ " " ++ show t ++ " " ++
        show t' ++ " " ++ show p ++ ")"

instance CMONO f g t t' p => IsProof (MONO f g t t' p) where

    type Lhs (MONO f g t t' p) = t
    type Rhs (MONO f g t t' p) = t'

    proof (MONO _ _ _ _ p) = proof p
    proxy'' _              = MONO
                                (proxy' Proxy)
                                (proxy' Proxy)
                                (proxy' Proxy)
                                (proxy' Proxy)
                                (proxy'' Proxy)

monoInj :: forall f g. CEql f g => f -> g -> Mono (Inj f g)
monoInj f g = Mono (Inj f g) $ \t t' (Proof p) -> Proof $ MONO f g t t' p
