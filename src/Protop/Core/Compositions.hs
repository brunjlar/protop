module Protop.Core.Compositions
    ( (:.)(..)
    , (:.|)(..)
    , (:|.)(..)
    , ASS(..)
    ) where

import Protop.Core.Morphisms
import Protop.Core.Proofs
import Protop.Core.Setoids
import Protop.Core.Singleton

type CComp a b = (IsMorphism a, IsMorphism b, Source a ~ Target b)

infixr 9 :.

data (:.) :: * -> * -> * where
    (:.) :: CComp a b => a -> b -> a :. b

instance Show (a :. b) where
    show (f :. g) = "(" ++ show f ++ " . " ++ show g ++ ")"

instance CComp a b => Singleton (a :. b) where
    singleton = singleton :. singleton

instance CComp a b => IsMorphism (a :. b) where
    type Source (a :. b) = Source b
    type Target (a :. b) = Target a
    onDomains (f :. g) = setComp (onDomains f) (onDomains g)

type CCOMPLEFT a b = (IsMorphism a, IsProof b, Source a ~ TARGET b)

infix :.|

data (:.|) :: * -> * -> * where
    (:.|) :: CCOMPLEFT a b => a -> b -> a :.| b

instance Show (a :.| b) where
    show (a :.| b) = "(" ++ show a ++ " . " ++ show b ++ ")"

instance CCOMPLEFT a b => Singleton (a :.| b) where
    singleton = singleton :.| singleton

instance CCOMPLEFT a b => IsProof (a :.| b) where

    type Lhs (a :.| b) = a :. Lhs b
    type Rhs (a :.| b) = a :. Rhs b

    proof (f :.| p) x = let Functoid _ g = onDomains f in g $ proof p x

type CCOMPRIGHT a b = (IsProof a, IsMorphism b, SOURCE a ~ Target b)

infix :|.

data (:|.) :: * -> * -> * where
    (:|.) :: CCOMPRIGHT a b => a -> b -> a :|. b

instance Show (a :|. b) where
    show (a :|. b) = "(" ++ show a ++ " . " ++ show b ++ ")"

instance CCOMPRIGHT a b => Singleton (a :|. b) where
    singleton = singleton :|. singleton

instance CCOMPRIGHT a b => IsProof (a :|. b) where
    type Lhs (a :|. b) = Lhs a :. b
    type Rhs (a :|. b) = Rhs a :. b
    proof (p :|. f) x = proof p $ f .$ x

type CASS a b c = (IsMorphism a, IsMorphism b, IsMorphism c, Source a ~ Target b, Source b ~ Target c)

data ASS :: * -> * -> * -> * where
    ASS :: CASS a b c => a -> b -> c -> ASS a b c

instance Show (ASS a b c) where
    show (ASS a b c) = "(ASS " ++ show a ++ " " ++ show b ++ " " ++ show c ++ ")"

instance CASS a b c => Singleton (ASS a b c) where
    singleton = ASS singleton singleton singleton

instance CASS a b c => IsProof (ASS a b c) where
    type Lhs (ASS a b c) = (a :. b) :. c
    type Rhs (ASS a b c) = a :. b :. c
    proof (ASS f g h) x = reflexivity $ f .$ g .$ h .$ x
