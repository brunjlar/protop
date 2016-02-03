{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Protop.Morphisms
    ( IsMorphism(..)
    , Morphism(..)
    , source
    , target
    , (.$)
    , MORPHISM(..)
    , apply
    ) where

import Data.Function  (on)
import Data.Proxy     (Proxy(..))
import Data.Typeable  (cast)
import Protop.Objects
import Protop.Setoids

class (Show a, IsObject (Source a), IsObject (Target a)) => IsMorphism a where

    type Source a
    type Target a

    onDomains :: a -> Functoid (Domain (Source a)) (Domain (Target a))
    proxy'    :: Proxy a -> a

data Morphism :: * -> * -> * where
    Morphism :: IsMorphism a => a -> Morphism (Source a) (Target a)

instance Show (Morphism a b) where

    show (Morphism f) = show f

instance Eq (Morphism a b) where

    (==) = (==) `on` show

instance Ord (Morphism a b) where

    compare = compare `on` show

source :: forall a. IsMorphism a => a -> Source a
source _ = proxy (Proxy :: Proxy (Source a))

target :: forall a. IsMorphism a => a -> Target a
target _ = proxy (Proxy :: Proxy (Target a))

infixr 1 .$

(.$) :: IsMorphism a => a -> Domain (Source a) -> Domain (Target a)
f .$ x = let Functoid g _ = onDomains f in g x

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
