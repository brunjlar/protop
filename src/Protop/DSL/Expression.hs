module Protop.DSL.Expression
    ( Exp (..)
    ) where

import           Data.Constraint      (Dict (..), withDict)
import           Data.Monoid          ((<>))
import qualified Data.Set             as S

import           Protop.DSL.Kind
import           Protop.DSL.Signature

type Sig = SigE Exp

data Exp (k :: Kind) :: * where
    Var    :: String -> Sig k -> Exp k
    App    :: Exp (LAM s t) -> Exp s -> Exp t
    Lambda :: String -> Sig k -> Exp l -> Exp (LAM k l)
    Sigma  :: String -> Sig k -> Sig l -> Exp k -> Exp l -> Exp (SGM k l)
    Pr1    :: Exp (SGM k l) -> Exp k
    Pr2    :: Exp (SGM k l) -> Exp l

instance Kinded Exp where

    typeable (Var _ s)         = typeable s
    typeable (App e _)         = case sig e of (Lam _ _ s) -> typeable s
    typeable (Lambda _ s e)    =
        withDict (typeable s) $
        withDict (typeable e) $
        Dict
    typeable (Sigma n s t _ _) = typeable (Sgm n s t)
    typeable (Pr1 e)           = case sig e of Sgm _ s _ -> typeable s
    typeable (Pr2 e)           = case sig e of Sgm _ _ s -> typeable s

    show' (Var n _)         = n
    show' (App e f)         = "(" ++ show' e ++ " " ++ show' f ++ ")"
    show' (Lambda n _ e)    = "(\\" ++ n ++ " -> " ++ show' e ++ ")"
    show' (Sigma _ _ _ e f) = "[" ++ show e ++ ", " ++ show f ++ "]"
    show' (Pr1 e)           = "(Pr1 " ++ show e ++ ")"
    show' (Pr2 e)           = "(Pr2 " ++ show e ++ ")"

    compare' (Var n s)         (Var n' s')            = compare n n' <> compare' s s'
    compare' (Var _ _)         _                      = LT
    compare' _                 (Var _ _)              = GT
    compare' (App e f)         (App e' f')            = compareK e e' <> compareK f f'
    compare' (App _ _)         _                      = LT
    compare' _                 (App _ _)              = GT
    compare' (Lambda n s e)    (Lambda n' s' e')      = case compare' s s' of
        LT -> LT
        GT -> GT
        EQ -> let (x, y) = alignNames n n' s e e' in compare x y
    compare' (Lambda _ _ _)    _                      = LT
    compare' _                 (Lambda _ _ _)         = GT
    compare' (Sigma n s t e f) (Sigma n' s' t' e' f') = compareK (Sgm n s t) (Sgm n' s' t') <>
                                                        compareK e e'                       <>
                                                        compareK f f'
    compare' (Sigma _ _ _ _ _) _                      = LT
    compare' _                 (Sigma _ _ _ _ _)      = GT
    compare' (Pr1 e)           (Pr1 e')               = compareK e e'
    compare' (Pr1 _)           _                      = LT
    compare' _                 (Pr1 _)                = GT
    compare' (Pr2 e)           (Pr2 e')               = compareK e e'

instance Show (Exp k) where

    show = show'

instance Eq (Exp k) where

    e == f = compare e f == EQ

instance Ord (Exp k) where

    compare = compare'

instance HasVar Exp where

    mkVar = Var

instance HasSig Exp Exp where

    sig (Var _ s)         = s
    sig (App e f)         = case sig e of
        Lam n s t -> subst n s f t
    sig (Lambda n s e)    = Lam n s (sig e)
    sig (Sigma n s t _ _) = Sgm n s t
    sig (Pr1 e)           = case sig e of Sgm _ s _ -> s
    sig (Pr2 e)           = case sig e of Sgm n s t -> subst n s (Pr1 e) t

    freeVars (Var n s)         = S.singleton $ UVar n (U s)
    freeVars (App e f)         = freeVars e `S.union` freeVars f
    freeVars (Lambda n s e)    = S.delete (UVar n (U s)) $ freeVars s `S.union` freeVars e
    freeVars (Sigma n s t e f) = S.delete (UVar n (U s)) $ freeVars s `S.union` freeVars t `S.union` freeVars e `S.union` freeVars f
    freeVars (Pr1 e)           = freeVars e
    freeVars (Pr2 e)           = freeVars e

    subst n s e (Var m t)
        | n /= m                       = Var m t
        | otherwise                    = caseEqK s t e (Var m t)
    subst n s e (App f g)              = App (subst n s e f) (subst n s e g)
    subst n s e (Lambda m t f)
        | UVar n (U s) == UVar m (U t) = Lambda m t f
        | otherwise                    = Lambda m (subst n s e t) (subst n s e f)
    subst n s e (Sigma m t u f g)
        | UVar n (U s) == UVar m (U t) = Sigma m t u f g
        | otherwise                    = Sigma m (subst n s e t) (subst n s e u) (subst n s e f) (subst n s e g)
    subst n s e (Pr1 f)                = Pr1 (subst n s e f)
    subst n s e (Pr2 f)                = Pr2 (subst n s e f)
