{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Protop.Utility
    ( eqT'
    , eqT''
    ) where

import Data.Maybe    (fromMaybe)
import Data.Proxy    (Proxy(..))
import Data.Typeable (Typeable, (:~:)(..), eqT, typeRep)

eqT' :: forall a b. (Typeable a, Typeable b) => a -> b -> a :~: b
eqT' _ _    = fromMaybe
                (error $ "incompatible types " ++
                    show (typeRep (Proxy :: Proxy a)) ++ " and " ++
                    show (typeRep (Proxy :: Proxy b)))
                eqT

eqT'' :: forall a b. (Typeable a, Typeable b) =>
            Proxy a -> Proxy b -> a :~: b
eqT'' pa pb = fromMaybe
                (error $ "incompatible types " ++
                    show (typeRep pa) ++ " and " ++
                    show (typeRep pb))
                eqT 
