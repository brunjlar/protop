{-# LANGUAGE UndecidableInstances #-}

module Protop.DSL.Signature
    ( SigE (..)
    , HasSig (..)
    , HasVar (..)
    , UVar (..)
    , alignNames
    ) where

import           Data.Constraint (Dict (..), withDict)
import           Data.Monoid     ((<>))
import           Data.Set (Set)
import qualified Data.Set as S

import           Protop.DSL.Kind

data SigE (e :: Kind -> *) (k :: Kind) :: * where
    Obj :: SigE e OBJ
    Mor :: e OBJ -> e OBJ -> SigE e MOR
    Prf :: e MOR -> e MOR -> SigE e PRF
    Lam :: String -> SigE e k -> SigE e l -> SigE e (LAM k l)
    Sgm :: String -> SigE e k -> SigE e l -> SigE e (SGM k l)

instance HasSig e e => Kinded (SigE e) where

    typeable Obj         = Dict
    typeable (Mor _ _)   = Dict
    typeable (Prf _ _)   = Dict
    typeable (Lam _ s t) =
        withDict (typeable s) $
        withDict (typeable t) $
        Dict
    typeable (Sgm _ s t) =
        withDict (typeable s) $
        withDict (typeable t) $
        Dict

    show' Obj         = "Obj"
    show' (Mor x y)   = "(" ++ show' x ++ " -> " ++ show' y ++ ")"
    show' (Prf f g)   = "(" ++ show' f ++ " == " ++ show' g ++ ")"
    show' (Lam n s t) = "(\\(" ++ show n ++ " :: " ++ show' s ++ ") --> " ++ show' t ++ ")"
    show' (Sgm n s t) = "[" ++ show n ++ " :: " ++ show' s ++ ", " ++ show' t ++ "]"

    compare' Obj         Obj              = EQ
    compare' (Mor x y)   (Mor x' y')      = compare' x x' <> compare' y y'
    compare' (Prf f g)   (Prf f' g')      = compare' f f' <> compare' g g'
    compare' (Lam n s t) (Lam n' s' t')   = case compare' s s' of
        LT -> LT
        GT -> GT
        EQ -> let (x, y) = alignNames n n' s t t' in compare x y
    compare' (Sgm n s t) (Sgm n' s' t')   = case compare' s s' of
        LT -> LT
        GT -> GT
        EQ -> let (x, y) = alignNames n n' s t t' in compare x y

instance HasSig e e => Show (SigE e k) where

    show = show'

instance HasSig e e => Eq (SigE e k) where

    s == t = compare s t == EQ

instance HasSig e e => Ord (SigE e k) where

    compare = compare'

data UVar e = UVar !String !(U (SigE e))
    deriving (Show, Eq, Ord)

class Kinded e => HasVar e where

    mkVar :: String -> SigE e k -> e k

class HasVar e => HasSig a e | a -> e where

    sig :: a k -> SigE e k

    freeVars :: a k -> Set (UVar e) 

    subst :: String -> SigE e k -> e k -> a l -> a l

instance HasSig e e => HasSig (SigE e) e where

    sig = id

    freeVars Obj         = S.empty
    freeVars (Mor x y)   = freeVars x `S.union` freeVars y
    freeVars (Prf f g)   = freeVars f `S.union` freeVars g
    freeVars (Lam n s t) = S.delete (UVar n (U s)) $ freeVars s `S.union` freeVars t
    freeVars (Sgm n s t) = S.delete (UVar n (U s)) $ freeVars s `S.union` freeVars t

    subst _ _ _ Obj         = Obj
    subst n s e (Mor x y)   = Mor (subst n s e x) (subst n s e y)
    subst n s e (Prf f g)   = Prf (subst n s e f) (subst n s e g)
    subst n s e (Lam m t u)
        | UVar n (U s) == UVar m (U t) = Lam m t u
        | otherwise                    = Lam m (subst n s e t) (subst n s e u)
    subst n s e (Sgm m t u)
        | UVar n (U s) == UVar m (U t) = Sgm m t u
        | otherwise                    = Sgm m (subst n s e t) (subst n s e u)

alignNames :: HasSig a e => String -> String-> SigE e k -> a l -> a l -> (a l, a l)
alignNames n n' s a a' =
    let vs = freeVars a `S.union` freeVars a'
        ns = S.map (\(UVar m' _) -> m') vs
        m  = head [m' | m' <- ['X' : show i | i <- [(1 :: Int) ..]]
                      , not (m' `S.member` ns)]
        v  = mkVar m s
    in  (subst n s v a, subst n' s v a')
