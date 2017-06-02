module Protop.Core.Morphisms
    ( IsMorphism(..)
    , DSource
    , DTarget
    , PSource
    , PTarget
    , Morphism(..)
    , onDomains'
    , source
    , target
    , (.$)
    , (.$.)
    , MORPHISM(..)
    , apply
    ) where

import Data.Function       (on)
import Data.Proxy          (Proxy(..))
import Data.Typeable       (Typeable, cast)
import Protop.Core.Objects
import Protop.Core.Setoids

class ( Show a 
      , Typeable a
      , IsObject (Source a)
      , IsObject (Target a)
      ) => IsMorphism a where

    type Source a
    type Target a

    onDomains :: a -> Functoid (DSource a) (DTarget a)
    proxy'    :: Proxy a -> a

type DSource f = Domain (Source f)
type DTarget f = Domain (Target f)
type PSource f = Proofs (DSource f)
type PTarget f = Proofs (DTarget f)

data Morphism :: * -> * -> * where
    Morphism :: IsMorphism a => a -> Morphism (Source a) (Target a)

instance Show (Morphism a b) where

    show (Morphism f) = show f

instance Eq (Morphism a b) where

    (==) = (==) `on` show

instance Ord (Morphism a b) where

    compare = compare `on` show

onDomains' :: Morphism a b -> Functoid (Domain a) (Domain b)
onDomains' (Morphism f) = onDomains f

source :: forall a. IsMorphism a => a -> Source a
source _ = proxy (Proxy :: Proxy (Source a))

target :: forall a. IsMorphism a => a -> Target a
target _ = proxy (Proxy :: Proxy (Target a))

infixr 1 .$

(.$) :: IsMorphism a => a -> DSource a -> DTarget a
f .$ x = let Functoid g _ = onDomains f in g x

infixr 1 .$.

(.$.) :: Morphism a b -> Domain a -> Domain b
(Morphism f) .$. x = f .$ x

data MORPHISM :: * where
    MORPHISM :: IsMorphism a => a -> MORPHISM

instance Show MORPHISM where

    show (MORPHISM f) = show f

instance Eq MORPHISM where

    (==) = (==) `on` show

instance Ord MORPHISM where

    compare = compare `on` show

apply :: (IsSetoid a, IsSetoid b) => MORPHISM -> a -> Maybe b
apply (MORPHISM f) x = do
   x' <- cast x
   cast $ f .$ x' 
