{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Protop.Core.Transitivities
    ( (:>)(..)
    ) where

import Data.Proxy          (Proxy(..))
import Protop.Core.Proofs
import Protop.Core.Setoids

infixl 9 :>

data (:>) :: * -> * -> * where
    (:>) :: ( IsProof a
            , IsProof b
            , Rhs a ~ Lhs b
            ) => a -> b -> a :> b

instance Show (a :> b) where

    show (p :> q) = "(" ++ show p ++ " > " ++ show q ++ ")"

instance ( IsProof a
         , IsProof b
         , Rhs a ~ Lhs b
         ) => IsProof (a :> b) where

    type Lhs (a :> b) = Lhs a
    type Rhs (a :> b) = Rhs b

    proof (p :> q) x = transitivity (Proxy :: Proxy (DTARGET a))
                                    (proof p x)
                                    (proof q x)
    proxy'' _ = proxy'' Proxy :> proxy'' Proxy
