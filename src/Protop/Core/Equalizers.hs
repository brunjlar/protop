{-# LANGUAGE UndecidableInstances #-}

module Protop.Core.Equalizers
    ( (:==)(..)
    , Inj(..)
    , INJ(..)
    , Eql(..)
    , MONOINJ(..)
    ) where

import Protop.Core.Compositions
import Protop.Core.Monos
import Protop.Core.Morphisms
import Protop.Core.Objects
import Protop.Core.Proofs
import Protop.Core.Setoids
import Protop.Core.Singleton

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

instance CEql f g => Singleton (f :== g) where
    singleton = singleton :== singleton

instance CEql f g => IsObject (f :== g) where
    type Domain (f :== g) = SetEql (Domain (Source f)) (DTarget f)

data Inj :: * -> * -> * where
    Inj :: CEql f g => f -> g -> Inj f g

instance (Show (Inj f g)) where
    show (Inj f g) = "(Inj " ++ show f ++ " " ++ show g ++ ")"

instance CEql f g => Singleton (Inj f g) where
    singleton = Inj singleton singleton

instance CEql f g => IsMorphism (Inj f g) where
    type Source (Inj f g) = f :== g
    type Target (Inj f g) = Source f
    onDomains _ = setInj

data INJ :: * -> * -> * where
    INJ :: CEql f g => f -> g -> INJ f g

instance (Show (INJ f g)) where
    show (INJ f g) = "(INJ " ++ show f ++ " " ++ show g ++ ")"

instance CEql f g => Singleton (INJ f g) where
    singleton = INJ singleton singleton

instance (CEql f g) => IsProof (INJ f g) where
    type Lhs (INJ f g) = f :. Inj f g
    type Rhs (INJ f g) = g :. Inj f g
    proof _ (SetEql _ px) = px

data MONOINJ :: * -> * -> * where
    MONOINJ :: CEql f g => f -> g -> MONOINJ f g

instance Show (MONOINJ f g) where
    show (MONOINJ f g) = "(MONOINJ " ++ show f ++ " " ++ show g ++ ")"

instance CEql f g => Singleton (MONOINJ f g) where
    singleton = MONOINJ singleton singleton

instance CEql f g => IsProof (MONOINJ f g) where
    type Lhs (MONOINJ f g) = MonoTest1 (Inj f g)
    type Rhs (MONOINJ f g) = MonoTest2 (Inj f g)
    proof (MONOINJ f g) t =
        case (MonoTest1 (Inj f g) .$ t, MonoTest2 (Inj f g) .$ t) of
            (SetEql _ py1, SetEql _ py2) ->
                (proof (MONOTEST $ Inj f g) t, py1, py2)

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

instance CEql' f g h p => Singleton (Eql f g h p) where
    singleton = Eql singleton singleton singleton singleton

instance CEql' f g h p => IsMorphism (Eql f g h p) where
    type Source (Eql f g h p) = Source h
    type Target (Eql f g h p) = f :== g
    onDomains (Eql _ _ h p) = Functoid h' h'' where
        h' z   = SetEql (h .$ z) $ proof p z
        h'' pz = (onProofs (onDomains h) pz,
                  proof p $ setLhs pz,
                  proof p $ setRhs pz)
