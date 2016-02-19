{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Protop.Logic.Types
    ( Kind(..)
    , Scope(..)
    , Sig
    , Entity
    , scopeS
    , scope
    ) where

{-
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
    , sig
    , show'
    ) where
-}

import Data.List       (intercalate)
import Numeric.Natural (Natural)
import Data.Proxy      (Proxy(..))
import Protop.Utility  ((:++))

data Kind =
    OBJ
  | MOR
  | PRF
  | LAM Kind Kind deriving (Show, Eq)

data Scope :: [Kind] -> * where

    Empty :: Scope '[]

    Cons :: Sig ks k -> Scope (k ': ks)

data Sig :: [Kind] -> Kind -> * where

    ObjS :: Scope ks -> Sig ks 'OBJ 

    MorS :: Entity ks 'OBJ -> Entity ks 'OBJ -> Sig ks 'MOR

    PrfS :: Entity ks 'MOR -> Entity ks 'MOR -> Sig ks 'PRF

    LamS :: Sig (k ': ks) k' -> Sig ks ('LAM k k')

data Entity :: [Kind] -> Kind -> * where

    Var :: Sig ks k -> Entity (k ': ks) k

    Lft :: Sig ks k -> Entity ks k' -> Entity (k ': ks) k' 

    Lam :: Entity (k ': ks) k' -> Entity ks ('LAM k k')

    App :: Entity ks ('LAM k k') -> Entity ks k -> Entity ks k'

instance Eq (Scope ks) where

    Empty  == Empty   = True
    Cons s == Cons s' = s == s'
    _      == _       = False

instance Eq (Sig ks k) where

    ObjS s   == ObjS s'    = s == s'
    MorS x y == MorS x' y' = x == x' && y == y'
    PrfS f g == PrfS f' g' = f == f' && g == g'
    LamS s   == LamS s'    = s == s'
    _        == _          = False

instance Eq (Entity ks k) where

    Var s   == Var s'    = s == s'
    Lft s e == Lft s' e' = s == s' && e == e'
    Lam e   == Lam e'    = e == e'
    App f e == App f' e' = show f == show f' && show e == show e'
    _       == _         = False

instance Show (Scope ks) where

    show sc = "{" ++ intercalate " > " (f sc) ++ "}" where

        f :: Scope ks' -> [String]
        f Empty = []
        f (Cons s) = show s : f (scopeS s)

instance Show (Sig ks k) where

    show (ObjS _) = "Ob"
    show (MorS x y) = "(" ++ show x ++ " -> " ++ show y ++ ")"
    show (PrfS f g) = "(" ++ show f ++ " == " ++ show g ++ ")"
    show (LamS t)   = let sc = scopeS t
                          s  = headSC sc
                      in  "((\\%" ++ show (1 + lengthSC sc) ++ " :: " ++
                          show s ++ ") -> " ++ show t ++ ")"

instance Show (Entity ks k) where

    show (Var s)   = "%" ++ show (1 + lengthSC (scopeS s))
    show (Lft _ e) = show e
    show (Lam e)   = let sc = scope e
                         s  = headSC sc
                     in  "((\\%" ++ show (1 + lengthSC sc) ++ " :: " ++
                         show s ++ ") -> " ++ show e ++ ")"
    show (App f e) = "(" ++ show f ++ " " ++ show e ++ ")"

scopeS :: Sig ks k -> Scope ks
scopeS (ObjS sc)  = sc
scopeS (MorS x _) = scope  x
scopeS (PrfS f _) = scope  f
scopeS (LamS s)   = tailSC $ scopeS s

scope :: Entity ks k -> Scope ks
scope (Var s)   = Cons s
scope (Lft s _) = Cons s
scope (Lam e)   = tailSC $ scope e
scope (App f _) = scope f

--sig :: Entity ks k -> Sig ks k
--sig (Var s)   = insertS 0 s s
--sig (Lft s e) = insertS 0 s $ sig e
--sig (Lam _ e) = LamS s (sig e) where
--    Scope sc = scope e
--    s = case head sc of SIG s' -> fromJust $ cast s'
--sig (App f e) = case sig f of LamS _ t -> substS 0 e t

tailSC :: Scope (k ': ks) -> Scope ks
tailSC (Cons s) = scopeS s

headSC :: Scope (k ': ks) -> Sig ks k
headSC (Cons s) = s

lengthSC :: Scope ks -> Natural
lengthSC Empty    = 0
lengthSC (Cons s) = 1 + lengthSC (scopeS s)

class Insertable (ls :: [Kind]) where

    insertSC :: Proxy ls ->
                Sig ks k -> Scope  (ls :++ ks) -> Scope  (ls :++ (k ': ks))

    insertS  :: Proxy ls ->
                Sig ks k -> Sig (ls :++ ks) l -> Sig (ls :++ (k ': ks)) l

    insert   :: Proxy ls ->
                Sig ks k -> Entity (ls :++ ks) l -> Entity (ls :++ (k ': ks)) l

instance Insertable '[] where

    insertSC _ s _ = Cons s

    insertS _ s (ObjS sc)  = ObjS (insertSC pE s sc)
    
    insertS _ s (MorS x y) = MorS (insert pE s x) (insert pE s y)
    insertS _ s (PrfS f g) = PrfS (insert pE s f) (insert pE s g)
    insertS _ s (LamS (t :: Sig (k ': ks) l))
                           = LamS (insertS (Proxy :: Proxy '[k]) s t)

    insert _ s (Var t)   = Lft s (Var t)
    insert _ s (Lft t e) = Lft s (Lft t e)
    insert _ s (Lam (e :: Entity (k ': ks) l))
                         = Lam (insert (Proxy :: Proxy '[k]) s e)
    insert _ s (App f e) = App (insert pE s f) (insert pE s e)

instance Insertable ls => Insertable (l ': ls) where

    insertSC _ s sc = Cons $ insertS (Proxy :: Proxy ls) s $ headSC sc

    insertS p s (ObjS sc)  = ObjS (insertSC p s sc)
    insertS p s (MorS x y) = MorS (insert p s x) (insert p s y)
    insertS p s (PrfS f g) = PrfS (insert p s f) (insert p s g)
    insertS _ (s :: Sig ks k) (LamS (t :: Sig (m ': ((l ': ls) :++ ks)) m'))
                           = LamS (insertS (Proxy :: Proxy (m ': l ': ls)) s t)

    insert _ s (Var t)   = Var (insertS (Proxy :: Proxy ls) s t) 
    insert _ s (Lft t e) = let p = Proxy :: Proxy ls
                           in  Lft (insertS p s t) (insert p s e)
    insert _ (s :: Sig ks k) (Lam (e :: Entity (m ': ((l ': ls) :++ ks)) m'))
                         = Lam (insert (Proxy :: Proxy (m ': l ': ls)) s e)
    insert p s (App f e) = App (insert p s f) (insert p s e)


pE :: Proxy ('[] :: [Kind])
pE = Proxy

--insert :: (Typeable k, Typeable k') => Natural -> Sig k -> Entity k' -> Entity k'
--insert 0 s e         = Lft s e
--insert n s (Var t)   = Var   (insertS (n - 1) s t)
--insert n s (Lft t e) = Lft t (insert  (n - 1) s e)
--insert n s (Lam p e) = Lam p (insert  (n + 1) s e)
--insert n s (App f e) = App (insert n s f) (insert n s e)

{-

instance Show (Sig k) where

    show (ObjS _)   = "Ob"
    show (MorS x y) = "(" ++ show x ++ " -> " ++ show y ++ ")"
    show (PrfS f g) = "(" ++ show f ++ " == " ++ show g ++ ")"
    show (LamS s t) = let Scope sc = scopeS s
                      in  "(\\(%" ++ show (1 + length sc) ++ " :: "
                          ++ show s ++ ") -> " ++ show t ++ ")"

instance Show (Entity k) where

    show (Var s)   = let Scope sc = scopeS s in "%" ++ show (1 + length sc)
    show (Lft _ e) = show e
    show (Lam _ e) = let Scope sc = scope e
                     in  "(\\(%" ++ show (length sc) ++ " :: "
                         ++ show (head sc) ++ ") -> " ++ show e ++ ")"
    show (App f e) = "(" ++ show f ++ " " ++ show e ++ ")"

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


lftS' :: Typeable k => Sig k -> Sig k' -> Either String (Sig k')
lftS' s t
    | scopeS s == scopeS t = Right $ insertS 0 s t
    | otherwise            = Left  $ "can't add " ++ show s ++ " (scope " ++ show (scopeS s) ++
                                     ") to " ++ show t ++ " (scope " ++ show (scopeS t) ++ ")"

lftS :: Typeable k => Sig k -> Sig k' -> Sig k'
lftS s t = fromRight $ lftS' s t

show' :: Entity k -> String
show' e = show e ++ " :: " ++ show (sig e)
-}
