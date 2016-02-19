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
    , lftS'
    , lftS
    , lam'
    , lam
    , app'
    , app
    , scopeS
    , scopeSIG
    , scope
    , sig
    , show'
    ) where

import Data.Maybe      (fromJust)
import Data.Proxy      (Proxy(..))
import Data.Typeable   (Typeable, cast, TypeRep, typeRep)
import Numeric.Natural (Natural)
import Protop.Utility  (fromRight)

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

cons :: SIG -> Scope
cons s = let Scope sc = scopeSIG s in Scope (s : sc)

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
scope (Var s)   = cons (SIG s)
scope (Lft s e) = cons (SIG s)
scope (Lam _ e) = let Scope sc = scope  e in Scope $ tail sc
scope (App f _) = scope f

objS :: Scope -> Sig 'OBJ
objS = ObjS

morS' :: Entity 'OBJ -> Entity 'OBJ -> Either String (Sig 'MOR)
morS' x y
    | scope x == scope y = Right $ MorS x y
    | otherwise          = Left $ "can't make morphism signature from " ++
                                  show x ++ " (scope " ++ show (scope x) ++
                                  ") and " ++
                                  show y ++ " (scope " ++ show (scope y) ++ ")"

morS :: Entity 'OBJ -> Entity 'OBJ -> Sig 'MOR
morS x y = fromRight $ morS' x y

prfS' :: Entity 'MOR -> Entity 'MOR -> Either String (Sig 'PRF)
prfS' f g
    | sig f == sig g = Right $ PrfS f g
    | otherwise      = Left $ "can't make proof signature from " ++
                              show' f ++ " and " ++ show' g

prfS :: Entity 'MOR -> Entity 'MOR -> Sig 'PRF
prfS f g = fromRight $ prfS' f g

lamS' :: forall k k'.
         ( Typeable k
         , Typeable k'
         ) => Proxy k -> Sig k' -> Either String (Sig ('LAM k k'))
lamS' _ t =
    case scopeS t of
        Scope []      ->
            Left "can't make lambda signature in empty scope"
        Scope (s : _) ->
            case s of
                SIG s' ->
                    case cast s' of
                        Just s'' ->Right $ LamS s'' t
                        Nothing  ->
                            Left $ show t ++ " doesn't have argument kind "
                                          ++ show (typeRep (Proxy :: Proxy k)) 

lamS :: (Typeable k, Typeable k') => Proxy k -> Sig k' -> Sig ('LAM k k')
lamS p t = fromRight $ lamS' p t

var :: Typeable k => Sig k -> Entity k
var = Var

lft' :: (Typeable k, Typeable k') => Sig k -> Entity k' -> Either String (Entity k')
lft' s e
    | scopeS s == scope e = Right $ Lft s e
    | otherwise           = Left $ "can't lift " ++ show' e ++ " (scope " ++
                                   show (scope e) ++ ") by signature " ++
                                   show s ++ " (scope " ++ show (scopeS s) ++ ")"

lft :: (Typeable k, Typeable k') => Sig k -> Entity k' -> Entity k'
lft s e = fromRight $ lft' s e

lam' :: ( Typeable k
        , Typeable k'
        ) => Proxy k -> Entity k' -> Either String (Entity ('LAM k k'))
lam' p e =
    case scope e of
        Scope []                     ->
            Left $ "can't make lambda from " ++ show' e ++ " (empty scope)"
        Scope (s : _)
            | typeRep p == kindRep s ->
                Right $ Lam p e
            | otherwise              ->
                Left $ "can't make lambda with argument kind " ++
                       show (typeRep p) ++ " from " ++ show' e

lam :: (Typeable k, Typeable k') => Proxy k -> Entity k' -> Entity ('LAM k k')
lam p e = fromRight $ lam' p e

app' :: ( Typeable k
        , Typeable k' 
        ) => Entity ('LAM k k') -> Entity k -> Either String (Entity k')
app' f e
    | scope f /= scope e =
        Left $ "can't apply " ++ show' f ++ " (scope " ++ show (scope f) ++
               ") to " ++ show' e ++ " (scope " ++ show (scope e)
    | otherwise          =
        case sig f of
            LamS s _ ->
                if sig e == s
                    then Right $ App f e
                    else Left $ "can't apply " ++ show' f ++
                                " to " ++ show' e

app :: (Typeable k, Typeable k') => Entity ('LAM k k') -> Entity k -> Entity k'
app f e = fromRight $ app' f e

insertSc :: Typeable k => Natural -> Sig k -> Scope -> Scope
insertSc 0 s sc                   = cons (SIG s)
insertSc n s (Scope (SIG t : ts)) = cons $ SIG $ insertS (n - 1) s t
insertSc _ _ (Scope [])           = error "can't insert into empty scope"

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

substSC :: Typeable k => Natural -> Entity k -> Scope -> Scope
substSC 0 e (Scope (_     : sc)) = Scope sc
substSC n e (Scope (SIG s : sc)) = cons $ SIG $ substS (n - 1) e s
substSC _ e (Scope [])           = error "can't substitute in empty scope"

substS :: Typeable k => Natural -> Entity k -> Sig k' -> Sig k'
substS n e (ObjS sc)  = ObjS (substSC n e sc) 
substS n e (MorS x y) = MorS (subst   n e x) (subst  n       e y)
substS n e (PrfS f g) = PrfS (subst   n e f) (subst  n       e g)
substS n e (LamS s t) = LamS (substS  n e s) (substS (n + 1) e t)

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

lftS' :: Typeable k => Sig k -> Sig k' -> Either String (Sig k')
lftS' s t
    | scopeS s == scopeS t = Right $ insertS 0 s t
    | otherwise            = Left  $ "can't add " ++ show s ++ " (scope " ++ show (scopeS s) ++
                                     ") to " ++ show t ++ " (scope " ++ show (scopeS t) ++ ")"

lftS :: Typeable k => Sig k -> Sig k' -> Sig k'
lftS s t = fromRight $ lftS' s t

show' :: Entity k -> String
show' e = show e ++ " :: " ++ show (sig e)
