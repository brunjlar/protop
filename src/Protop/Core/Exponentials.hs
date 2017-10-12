module Protop.Core.Exponentials
    ( (:->)(..)
    , Curry(..)
    , Uncurry(..)
    , UNCC(..)
    , CUNC(..)
    , Eval
    , eval
    ) where

import Protop.Core.Identities
import Protop.Core.Morphisms
import Protop.Core.Objects
import Protop.Core.Products
import Protop.Core.Proofs
import Protop.Core.Setoids
import Protop.Core.Singleton

infixr 1 :->

type CExp x y = (IsObject x, IsObject y)

data (:->) :: * -> * -> * where
    (:->) :: CExp x y => x -> y -> x :-> y

instance Show (x :-> y) where
    show (x :-> y) = "(" ++ show x ++ " -> " ++ show y ++ ")"

instance CExp x y => Singleton (x :-> y) where
    singleton = singleton :-> singleton

instance CExp x y => IsObject (x :-> y) where

    type Domain (x :-> y) = Functoid (Domain x) (Domain y)

type CCurry x y f = ( IsObject x
                    , IsObject y
                    , IsMorphism f
                    , Source f ~ (x :* y)
                    )

data Curry :: * -> * -> * -> * where
    Curry :: CCurry x y f => x -> y -> f -> Curry x y f

instance Show (Curry x y f) where
    show (Curry _ _ f) = "(Curry " ++ show f ++ ")"

instance CCurry x y f => Singleton (Curry x y f) where
    singleton = Curry singleton singleton singleton

instance CCurry x y f => IsMorphism (Curry x y f) where
    type Source (Curry x y f) = x
    type Target (Curry x y f) = y :-> Target f
    onDomains (Curry _ _ f) = setCurry $ onDomains f

type CUncurry f y z = ( IsMorphism f
                      , IsObject y
                      , IsObject z
                      , Target f ~ (y :-> z)
                      )

data Uncurry :: * -> * -> * -> * where
    Uncurry :: CUncurry f y z => f -> y -> z -> Uncurry f y z

instance Show (Uncurry f y z) where
    show (Uncurry f _ _) = "(Uncurry " ++ show f ++ ")"

instance CUncurry f y z => Singleton (Uncurry f y z) where
    singleton = Uncurry singleton singleton singleton

instance CUncurry f y z => IsMorphism (Uncurry f y z) where
    type Source (Uncurry f y z) = Source f :* y
    type Target (Uncurry f y z) = z
    onDomains (Uncurry f _ _) = setUncurry $ onDomains f

data UNCC :: * -> * -> * -> * where
    UNCC :: CCurry x y f => x -> y -> f -> UNCC x y f

instance Show (UNCC x y f) where
    show (UNCC _ _ f) = "(UNCC " ++ show f ++ ")"

instance CCurry x y f => Singleton (UNCC x y f) where
    singleton = UNCC singleton singleton singleton

instance CCurry x y f => IsProof (UNCC x y f) where
    type Lhs (UNCC x y f) = Uncurry (Curry x y f) y (Target f)
    type Rhs (UNCC x y f) = f
    proof (UNCC _ _ f) xy = reflexivity $ f .$ xy

data CUNC :: * -> * -> * -> * where
    CUNC :: CUncurry f y z => f -> y -> z -> CUNC f y z

instance Show (CUNC f y z) where
    show (CUNC f _ _) = "(CUNC " ++ show f ++ ")"

instance CUncurry f y z => Singleton (CUNC f y z) where
    singleton = CUNC singleton singleton singleton

instance CUncurry f y z => IsProof (CUNC f y z) where
    type Lhs (CUNC f y z) = Curry (Source f) y (Uncurry f y z)
    type Rhs (CUNC f y z) = f
    proof (CUNC f y z) x =
        ( Curry (source f) y (Uncurry f y z) .$ x
        , f                                  .$ x
        , onProofs $ f .$ x
        )

type Eval x y = Uncurry (Id (x :-> y)) x y

eval :: (IsObject x, IsObject y) => x -> y -> Eval x y
eval x y = Uncurry (Id $ x :-> y) x y
