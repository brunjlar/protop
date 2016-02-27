{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

module Protop.TVault
    ( TVault
    , empty
    , insert
    , lookup
    ) where

import           Data.Proxy           (Proxy(..))
import qualified Data.Map      as M
import           Data.Typeable        (Typeable, typeRep, TypeRep, cast)
import           Prelude       hiding (lookup)

data Wrapper where

    Wrap :: Typeable a => a -> Wrapper

newtype TVault = TVault (M.Map TypeRep Wrapper)

empty :: TVault
empty = TVault M.empty

insert :: forall a. Typeable a => a -> TVault -> TVault
insert a (TVault m) = let key   = typeRep (Proxy :: Proxy a)
                          value = Wrap a
                      in  TVault (M.insert key value m)

lookup :: forall a. Typeable a => Proxy a -> TVault -> Maybe a
lookup _ (TVault m) = do
    let key = typeRep (Proxy :: Proxy a)
    Wrap a <- M.lookup key m
    cast a
