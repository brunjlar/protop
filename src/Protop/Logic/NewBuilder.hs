{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Protop.Logic.NewBuilder
    (
    ) where

import Data.List          (intercalate)
import Protop.Logic.Types

data ST :: [Kind] -> * where

    EmptyST :: ST '[]

    ConsST  :: String -> Sig k ks -> ST ks -> ST (k ': ks)

instance HasScope ST where

    scope EmptyST        = Empty
    scope (ConsST _ s _) = Cons s

instance Eq (ST ks) where

    EmptyST      == EmptyST         = True
    ConsST n s t == ConsST n' s' t' = n == n' && s == s' && t == t'
    _            == _               = False

instance Show (ST ks) where

    show EmptyST = "{}"
    show st      = "{" ++ intercalate ", " (f st) ++ "}" where

        f :: ST ks' -> [String]
        f EmptyST = []
        f (ConsST n s t) = (n ++ " :: " ++ show s) : f t
