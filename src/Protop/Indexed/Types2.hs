{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Protop.Indexed.Types
    ( Sig
    , objS
    , morS
    , var
    , lft
    ) where

import Data.Typeable (Typeable, cast)

data Kind =
    OBJ
  | MOR
  | PRF
  | LAM Kind Kind deriving (Show, Eq)

data Sig :: [Kind] -> Kind -> * where

    ObjS :: Typeable ks => Sig ks 'OBJ
    MorS :: Typeable ks => Entity ks 'OBJ -> Entity ks 'OBJ -> Sig ks 'MOR

instance Eq (Sig ks k) where

    ObjS     == ObjS       = True
    MorS x y == MorS x' y' = x == x' && y == y'
    _        == _          = False

data SIG :: * where

    SIG :: (Typeable ks, Typeable k) => Sig ks k -> SIG

instance Eq SIG where

    SIG s == SIG t = case cast s of
                        Just s' -> s' == t
                        Nothing -> False

objS :: Typeable ks => Sig ks 'OBJ
objS = ObjS

morS :: Typeable ks => Entity ks 'OBJ -> Entity ks 'OBJ -> Maybe (Sig ks 'MOR)
morS x y = case (getVar x, getVar y) of
                (Just s, Just s') -> if s == s' then Just (MorS x y) else Nothing
                _                 -> Just (MorS x y)

data Entity :: [Kind] -> Kind -> * where

    Var :: (Typeable ks, Typeable k) => Sig ks k -> Entity (k ': ks) k
    Lft :: (Typeable ks, Typeable k) => Entity ks k -> Entity (k' ': ks) k

instance Eq (Entity ks k) where

    Var s == Var s' = s == s'
    Lft e == Lft e' = e == e'
    _     == _      = False

var :: (Typeable ks, Typeable k) => Sig ks k -> Entity (k ': ks) k
var = Var

lft :: (Typeable ks, Typeable k) => Entity ks k -> Entity (k' ': ks) k
lft = Lft

getVar :: Entity ks k -> Maybe SIG
getVar (Var s) = Just $ SIG s
getVar (Lft _) = Nothing
