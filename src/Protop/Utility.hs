{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

module Protop.Utility
    ( Typeable
    , (:~:)(..)
    , typeRep
    , eqT
    , eqT'
    , eqT''
    , decEq
    , fromRight
    ) where

import Data.Maybe    (fromMaybe, isJust)
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

decEq :: forall a b. (Typeable a, Typeable b) => a -> b -> Bool
decEq _ _ = isJust (eqT :: Maybe (a :~: b))

fromRight :: Either String a -> a
fromRight (Right x) = x
fromRight (Left e)  = error e
