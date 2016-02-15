{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}

module Protop.Indexed.Types
    ( Kind(..)
    , Sig'
    , objS
    , morS
    , lamS
    , Entity'
    , var
    , axiomObj
    , axiomMor
    , axiomLam
    , toObject
    , source
    , target
    , lhs
    , rhs
    , sig
    , show'
    ) where

import           Data.Proxy      (Proxy(..))
import           Data.Typeable   (Typeable, eqT, (:~:)(..))
import           GHC.TypeLits
import           Numeric.Natural (Natural)
import qualified Protop.Core     as C

data Kind =
    OBJ
  | MOR
  | PRF
  | LAM Kind Kind deriving (Show, Eq)

class HasLevel a where

    level :: a -> Natural

data Sig' :: Nat -> Kind -> * where

    ObjS :: Natural -> Sig' n 'OBJ
    MorS :: Entity' n 'OBJ -> Entity' n 'OBJ -> Sig' n 'MOR
    PrfS :: Entity' n 'MOR -> Entity' n 'MOR -> Sig' n 'PRF
    LamS :: (Typeable k, Typeable k') =>
            Sig' n k -> Sig' (n + 1) k' -> Sig' n ('LAM k k')

objS :: forall n. KnownNat n => Sig' n 'OBJ
objS = ObjS $ fromInteger $ natVal (Proxy :: Proxy n)

morS :: Entity' n 'OBJ -> Entity' n 'OBJ -> Sig' n 'MOR
morS = MorS

lamS :: (Typeable k, Typeable k') =>
        Sig' n k -> Sig' (n + 1) k' -> Sig' n ('LAM k k') 
lamS = LamS

instance HasLevel (Sig' n k) where

    level (ObjS n) = n
    level (MorS x _) = level x
    level (PrfS f _) = level f
    level (LamS s _) = level s

instance Show (Sig' n k) where

    show (ObjS _  ) = "Ob"
    show (MorS x y) = show x ++ " -> " ++ show y
    show (PrfS f g) = show f ++ " == " ++ show g ++ " :: " ++ show (sig f)
    show (LamS s t) = "(" ++ show' (Var s) ++ ") ~> " ++ show t

instance Eq (Sig' n k) where

    s == s' = show s == show s'

data Entity' :: Nat -> Kind -> * where

    AxiomObj :: C.IsObject   x => x -> Entity' 0 'OBJ
    AxiomMor :: C.IsMorphism f => f -> Entity' 0 'MOR
    AxiomPrf :: C.IsProof    p => p -> Entity' 0 'PRF
    AxiomLam :: (Typeable k, Typeable k') =>
                String -> Sig' n k -> Sig' (n + 1) k' ->
                (Entity' n k -> Entity' n k') -> Entity' n ('LAM k k')
    Lft      :: Typeable k => Entity' n k -> Entity' (n + 1) k
    Var      :: Typeable k => Sig' n k -> Entity' (n + 1) k
    App      :: (Typeable k, Typeable k') =>
                Entity' n ('LAM k k') -> Entity' n k -> Entity' n k'
    Lam      :: (Typeable k, Typeable k') =>
                Sig' n k -> Entity' (n + 1) k' -> Entity' n ('LAM k k')

var :: Typeable k => Sig' n k -> Entity' (n + 1) k
var = Var

axiomObj :: C.IsObject x => x -> Entity' 0 'OBJ
axiomObj = AxiomObj

axiomMor :: C.IsMorphism f => f -> Entity' 0 'MOR
axiomMor = AxiomMor

axiomLam :: (Typeable k, Typeable k') =>
            String -> Sig' n k -> Sig' (n + 1) k' ->
            (Entity' n  k -> Entity' n k') -> Entity' n ('LAM k k')
axiomLam = AxiomLam

toObject :: Entity' 0 'OBJ -> C.Object
toObject (AxiomObj x) = C.Object x
toObject _            = error "impossible case"

instance HasLevel (Entity' n k) where

    level (AxiomObj _)       = 0
    level (AxiomMor _)       = 0
    level (AxiomPrf _)       = 0
    level (AxiomLam _ s _ _) = level s
    level (Lft e)            = 1 + level e
    level (Var s)            = 1 + level s
    level (App s _)          = level s
    level (Lam s _)          = level s

instance Show (Entity' n k) where

    show (AxiomObj x)       = show x
    show (AxiomMor f)       = show f
    show (AxiomPrf p)       = show p
    show (AxiomLam c _ _ _) = c
    show (Lft e)            = show e
    show (Var v)            = "%" ++ (show $ succ $ level v)
    show (App e e')         = "(" ++ show e ++ " " ++ show e' ++ ")"
    show (Lam s e)          = "(\\(%" ++ (show $ level e) ++ " :: " ++
                              show s ++ ") -> " ++ show e ++ ")"

source, target :: Entity' n 'MOR -> Entity' n 'OBJ
source f = let MorS s _ = sig f in s
target f = let MorS _ t = sig f in t

lhs, rhs :: Entity' n 'PRF -> Entity' n 'MOR
lhs p = let PrfS l _ = sig p in l
rhs p = let PrfS _ r = sig p in r

lftS :: Sig' n k -> Sig' (n + 1) k
lftS (ObjS n  ) = ObjS (n + 1)
lftS (MorS x y) = MorS (Lft x) (Lft y)
lftS (PrfS f g) = PrfS (Lft f) (Lft g)
lftS (LamS s t) = LamS (lftS s) (lftS t)

substS :: forall n k k'. (Typeable k, Typeable k') =>
          Sig' (n + 1) k -> Entity' n k' -> Sig' n k
substS (ObjS n')   _ = ObjS (n' - 1) 
substS (MorS x y)  e = MorS (substE x e) (substE y e)
substS (PrfS f g)  e = PrfS (substE f e) (substE g e)
substS (LamS s s') e = LamS (substS s e) (substS s' $ Lft e)

substE :: forall n k k'. (Typeable k, Typeable k') =>
          Entity' (n + 1) k -> Entity' n k' -> Entity' n k
substE (Lft e)       _ = e
substE (Var s)       f =
    case eqT :: Maybe (k :~: k') of
        Just Refl -> f
        Nothing   -> error $ "can't substitute " ++ show' f ++ " for " ++
                             show' (Var s)
substE (Lam s e)  f  = Lam (substS s f) (substE e $ Lft f) 
substE (App e e') f  = App (substE e f) (substE e' f)
substE e          f  = error $ "can't substitue " ++ show' f ++ " for " ++
                               show' e

sig :: Entity' n k -> Sig' n k
sig e@(AxiomObj _)       = ObjS (level e)
sig   (AxiomMor f)       = MorS (AxiomObj $ C.source f)
                                (AxiomObj $ C.target f)
sig   (AxiomPrf p)       = PrfS (AxiomMor $ C.lhs    p)
                                (AxiomMor $ C.rhs    p)
sig   (AxiomLam _ s t _) = LamS s t
sig   (Lft e)            = lftS (sig e)
sig   (Var s)            = lftS s
sig   (App e e')         = case sig e of LamS _ s -> substS s e'
sig   (Lam s e)          = LamS s (sig e)

show' :: Entity' n k -> String
show' e = show e ++ " :: " ++ show (sig e)
