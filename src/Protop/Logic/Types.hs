{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Protop.Logic.Types
    ( Kind(..)
    , HasKindRep(..)
    , Sig
    , SIG(..)
    , Entity
    , Scope
    , empty
    , cons'
    , cons
    , objS
    , morS'
    , morS
    , prfS'
    , prfS
    , lamS'
    , lamS
    , var
    , lft
    , lft'
    , lam'
    , lam
    , app'
    , app
    , scopeS
    , scopeSIG
    , scope
    , sig
    ) where

import Data.Maybe      (fromJust)
import Data.Proxy      (Proxy(..))
import Data.Typeable   (Typeable, cast, TypeRep, typeRep)
import Numeric.Natural (Natural)

data Kind =
    OBJ
  | MOR
  | PRF
  | LAM Kind Kind deriving (Show, Eq)

class HasKindRep a where

    kindRep :: a -> TypeRep

data Sig :: Kind -> * where

    ObjS :: Scope -> Sig 'OBJ 

    MorS :: Entity 'OBJ -> Entity 'OBJ -> Sig 'MOR

    PrfS :: Entity 'MOR -> Entity 'MOR -> Sig 'PRF

    LamS :: (Typeable k, Typeable k') => Sig k -> Sig k' -> Sig ('LAM k k')

instance HasKindRep (Sig k) where

    kindRep (ObjS _)   = typeRep (Proxy :: Proxy k)
    kindRep (MorS _ _) = typeRep (Proxy :: Proxy k)
    kindRep (PrfS _ _) = typeRep (Proxy :: Proxy k)
    kindRep (LamS _ _) = typeRep (Proxy :: Proxy k)

instance Eq (Sig k) where

    ObjS s   == ObjS s'    = s == s'
    MorS x y == MorS x' y' = x == x' && y == y'
    PrfS f g == PrfS f' g' = f == f' && g == g'
    LamS s t == LamS s' t' = s == s' && t == t'
    _        == _          = False

instance Show (Sig k) where

    show (ObjS _)   = "Ob"
    show (MorS x y) = "(" ++ show x ++ " -> " ++ show y ++ ")"
    show (PrfS f g) = "(" ++ show f ++ " == " ++ show g ++ ")"
    show (LamS s t) = let Scope sc = scopeS s
                      in  "(\\(%" ++ show (1 + length sc) ++ " :: "
                          ++ show s ++ ") -> " ++ show t ++ ")"

scopeS :: Sig k -> Scope
scopeS (ObjS s)   = s
scopeS (MorS x _) = scope  x
scopeS (PrfS f _) = scope  f
scopeS (LamS s _) = scopeS s

data SIG :: * where

    SIG :: Typeable k => Sig k -> SIG

instance HasKindRep SIG where

    kindRep (SIG s) = kindRep s

instance Eq SIG where

    SIG s == SIG t = case cast s of
                        Just s' -> s' == t
                        Nothing -> False

instance Show SIG where

    show (SIG s) = show s

scopeSIG :: SIG -> Scope
scopeSIG (SIG s) = scopeS s

newtype Scope = Scope [SIG] deriving (Show, Eq)

empty :: Scope
empty = Scope []

cons' :: SIG -> Scope -> Maybe Scope
cons' s sc
    | scopeSIG s == sc = let Scope sc' = sc in Just $ Scope $ s : sc'
    | otherwise        = Nothing

cons :: SIG -> Scope -> Scope
cons s sc = fromJust $ cons' s sc

data Entity :: Kind -> * where

    Var :: Typeable k => Sig k -> Entity k
    Lft :: (Typeable k, Typeable k') => Sig k -> Entity k' -> Entity k' 
    Lam :: (Typeable k, Typeable k') => Proxy k -> Entity k' -> Entity ('LAM k k')
    App :: (Typeable k, Typeable k') => Entity ('LAM k k') -> Entity k -> Entity k'

instance HasKindRep (Entity k) where

    kindRep (Var _)   = typeRep (Proxy :: Proxy k)
    kindRep (Lft _ _) = typeRep (Proxy :: Proxy k)
    kindRep (Lam _ _) = typeRep (Proxy :: Proxy k)
    kindRep (App _ _) = typeRep (Proxy :: Proxy k)

instance Eq (Entity k) where

    Var s   == Var s'    = s == s'
    Lft s e == Lft s' e' = SIG s == SIG s' && e == e'
    Lam _ e == Lam _  e' = e == e'
    App f e == App f' e' = case (cast f', cast e') of
                                (Just f'', Just e'') -> f == f'' && e == e''
                                _                    -> False
    _       == _         = False

instance Show (Entity k) where

    show (Var s)   = let Scope sc = scopeS s in "%" ++ show (1 + length sc)
    show (Lft _ e) = show e
    show (Lam _ e) = let Scope sc = scope e
                     in  "(\\(%" ++ show (length sc) ++ " :: "
                         ++ show (head sc) ++ ") -> " ++ show e ++ ")"
    show (App f e) = "(" ++ show f ++ " " ++ show e ++ ")"

scope :: Entity k -> Scope
scope (Var s)   = cons (SIG s) $ scopeS s
scope (Lft s e) = cons (SIG s) $ scope  e
scope (Lam _ e) = let Scope sc = scope  e in Scope $ tail sc
scope (App f _) = scope f

objS :: Scope -> Sig 'OBJ
objS = ObjS

morS' :: Entity 'OBJ -> Entity 'OBJ -> Maybe (Sig 'MOR)
morS' x y
    | scope x == scope y = Just $ MorS x y
    | otherwise          = Nothing

morS :: Entity 'OBJ -> Entity 'OBJ -> Sig 'MOR
morS x y = fromJust $ morS' x y

prfS' :: Entity 'MOR -> Entity 'MOR -> Maybe (Sig 'PRF)
prfS' f g
    | sig f == sig g = Just $ PrfS f g
    | otherwise      = Nothing

prfS :: Entity 'MOR -> Entity 'MOR -> Sig 'PRF
prfS f g = fromJust $ prfS' f g

lamS' :: (Typeable k, Typeable k') => Proxy k -> Sig k' -> Maybe (Sig ('LAM k k'))
lamS' _ t = case scopeS t of
                Scope []      -> Nothing
                Scope (s : _) -> case s of SIG s' -> case cast s' of
                                                        Just s'' -> Just $ LamS s'' t
                                                        Nothing  -> Nothing

lamS :: (Typeable k, Typeable k') => Proxy k -> Sig k' -> Sig ('LAM k k')
lamS p t = fromJust $ lamS' p t

var :: Typeable k => Sig k -> Entity k
var = Var

lft' :: (Typeable k, Typeable k') => Sig k -> Entity k' -> Maybe (Entity k')
lft' s e
    | scopeS s == scope e = Just $ Lft s e
    | otherwise           = Nothing

lft :: (Typeable k, Typeable k') => Sig k -> Entity k' -> Entity k'
lft s e = fromJust $ lft' s e

lam' :: (Typeable k, Typeable k') => Proxy k -> Entity k' -> Maybe (Entity ('LAM k k'))
lam' p e = case scope e of
                Scope []                     -> Nothing
                Scope (s : _)
                    | typeRep p == kindRep s -> Just $ Lam p e
                    | otherwise              -> Nothing

lam :: (Typeable k, Typeable k') => Proxy k -> Entity k' -> Entity ('LAM k k')
lam p e = fromJust $ lam' p e

app' :: (Typeable k, Typeable k') => Entity ('LAM k k') -> Entity k -> Maybe (Entity k')
app' f e
    | scope f /= scope e = Nothing
    | otherwise          =
        case sig f of
            LamS s _ -> if sig e == s
                            then Just $ App f e
                            else Nothing

app :: (Typeable k, Typeable k') => Entity ('LAM k k') -> Entity k -> Entity k'
app f e = fromJust $ app' f e

insertSc :: Typeable k => Natural -> Sig k -> Scope -> Scope
insertSc 0 s sc               = cons (SIG s) sc
insertSc n s (Scope (t : ts)) = cons t $ insertSc (n - 1) s $ Scope ts
insertSc _ _ (Scope [])       = error "can't insert into empty scope"

insertS :: Typeable k => Natural -> Sig k -> Sig k' -> Sig k'
insertS n s (ObjS sc)  = ObjS (insertSc n s sc)
insertS n s (MorS x y) = MorS (insert   n s x) (insert  n       s y)
insertS n s (PrfS f g) = PrfS (insert   n s f) (insert  n       s g)
insertS n s (LamS u v) = LamS (insertS  n s u) (insertS (n + 1) s v)

insert :: (Typeable k, Typeable k') => Natural -> Sig k -> Entity k' -> Entity k'
insert 0 s e         = Lft s e
insert n s (Var t)   = Var   (insertS (n - 1) s t)
insert n s (Lft t e) = Lft t (insert  (n - 1) s e)
insert n s (Lam p e) = Lam p (insert  (n + 1) s e)
insert n s (App f e) = App (insert n s f) (insert n s e)

substSC :: Natural -> Scope -> Scope
substSC 0 (Scope (_ : sc)) = Scope sc
substSC n (Scope (s : sc)) = cons s $ substSC (n - 1) $ Scope sc
substSC _ (Scope [])       = error "can't substitute in empty scope"

substS :: Typeable k => Natural -> Entity k -> Sig k' -> Sig k'
substS n _ (ObjS sc)  = ObjS (substSC n sc) 
substS n e (MorS x y) = MorS (subst  n e x) (subst  n       e y)
substS n e (PrfS f g) = PrfS (subst  n e f) (subst  n       e g)
substS n e (LamS s t) = LamS (substS n e s) (substS (n + 1) e t)

subst :: Typeable k => Natural -> Entity k -> Entity k' -> Entity k'
subst 0 e (Var _)   = fromJust $ cast e
subst n e (Var s)   = Var (substS (n - 1) e s)
subst 0 _ (Lft _ f) = f
subst n e (Lft s f) = Lft s (subst (n - 1) e f)
subst n e (Lam p f) = Lam p (subst (n + 1) e f)
subst n e (App f g) = App (subst n e f) (subst n e g)

sig :: Entity k -> Sig k
sig (Var s)   = insertS 0 s s
sig (Lft s e) = insertS 0 s $ sig e
sig (Lam _ e) = LamS s (sig e) where
    Scope sc = scope e
    s = case head sc of SIG s' -> fromJust $ cast s'
sig (App f e) = case sig f of LamS _ t -> substS 0 e t
