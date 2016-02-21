{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Protop.Logic.Types
    ( Kind(..)
    , Scope(..)
    , headSC
    , tailSC
    , Sig
    , Entity
    , HasScope(..)
    , lft'
    , lft
    , sig
    , objS
    , morS'
    , morS
    , prfS'
    , prfS
    , lamS
    , var
    , lam
    , app'
    , app
    , show'
    ) where

import Data.List       (intercalate)
import Numeric.Natural (Natural)
import Data.Proxy      (Proxy(..))
import Protop.Utility  ((:++), fromRight)

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

    ObjS sc  == ObjS sc'   = sc == sc'
    MorS x y == MorS x' y' = x  == x' && y == y'
    PrfS f g == PrfS f' g' = f  == f' && g == g'
    LamS s   == LamS s'    = s  == s'
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
        f (Cons s) = show s : f (scope s)

instance Show (Sig ks k) where

    show (ObjS _) = "Ob"
    show (MorS x y) = "(" ++ show x ++ " -> " ++ show y ++ ")"
    show (PrfS f g) = "(" ++ show f ++ " == " ++ show g ++ ")"
    show (LamS t)   = let sc = scope t
                          s  = headSC sc
                      in  "(\\(%" ++ show (lengthSC sc) ++ " :: " ++
                          show s ++ ") -> " ++ show t ++ ")"

instance Show (Entity ks k) where

    show (Var s)   = "%" ++ show (1 + lengthSC (scope s))
    show (Lft _ e) = show e
    show (Lam e)   = let sc = scope e
                         s  = headSC sc
                     in  "(\\(%" ++ show (lengthSC sc) ++ " :: " ++
                         show s ++ ") -> " ++ show e ++ ")"
    show (App f e) = "(" ++ show f ++ " " ++ show e ++ ")"

class HasScope (a :: [Kind] -> Kind -> *) where

    scope :: a ks k -> Scope ks

instance HasScope Sig where

    scope (ObjS sc)  = sc
    scope (MorS x _) = scope  x
    scope (PrfS f _) = scope  f
    scope (LamS s)   = tailSC $ scope s

instance HasScope Entity where

    scope (Var s)   = Cons s
    scope (Lft s _) = Cons s
    scope (Lam e)   = tailSC $ scope e
    scope (App f _) = scope f

class Liftable (a :: [Kind] -> Kind -> *) where

    lft_ :: Sig ks k -> a ks k' -> a (k ': ks) k'

instance Liftable Sig where

    lft_ = insertS pE

instance Liftable Entity where

    lft_ = insert pE

lft' :: ( Show (a ks k')
        , HasScope a
        , Liftable a
        ) => Sig ks k -> a ks k' -> Either String (a (k ': ks) k')
lft' s x = let ss = scope s
               sx = scope x
           in if ss == sx
                then Right $ lft_ s x
                else Left  $ "can't lift " ++ show x ++ " (" ++ show sx ++
                             ") to " ++ show s ++ " (" ++ show ss ++ ")"

lft :: ( Show (a ks k')
       , HasScope a
       , Liftable a
       ) => Sig ks k -> a ks k' -> a (k ': ks) k'
lft s x = fromRight $ lft' s x

sig :: Entity ks k -> Sig ks k
sig (Var s)   = lft s s
sig (Lft s e) = lft s $ sig e
sig (Lam s)   = LamS (sig s)
sig (App f e) = case sig f of LamS s -> substS pE e s 

show' :: Entity ks k -> String
show' e = show e ++ " :: " ++ show (sig e)

objS :: Scope ks -> Sig ks 'OBJ
objS = ObjS

morS' :: Entity ks 'OBJ -> Entity ks 'OBJ -> Either String (Sig ks 'MOR)
morS' x y = let scX = scope x
                scY = scope y
            in  if scX == scY
                    then Right $ MorS x y
                    else Left  $ "can't make morphism signature from objects " ++
                                 show x ++ " (" ++ show scX ++ ") and " ++
                                 show y ++ " (" ++ show scY ++ ")"

morS :: Entity ks 'OBJ -> Entity ks 'OBJ -> Sig ks 'MOR
morS x y = fromRight $ morS' x y

prfS' :: Entity ks 'MOR -> Entity ks 'MOR -> Either String (Sig ks 'PRF)
prfS' f g = let scF = scope f
                scG = scope g
            in if scF == scG && sig f == sig g
                then Right $ PrfS f g
                else Left  $ "can't make proof signature from morphisms " ++
                             show f ++ " (" ++ show scF ++ ") and " ++
                             show g ++ " (" ++ show scG ++ ")"

prfS :: Entity ks 'MOR -> Entity ks 'MOR -> Sig ks 'PRF
prfS f g = fromRight $ prfS' f g

lamS :: Sig (k ': ks) k' -> Sig ks ('LAM k k')
lamS = LamS

var :: Sig ks k -> Entity (k ': ks) k
var = Var

lam :: forall k k' ks. Entity (k ': ks) k' -> Entity ks ('LAM k k')
lam (App (Lft _ e) (Var _)) = e     -- eta reduction
lam e                       = Lam e

app' :: Entity ks ('LAM k k') -> Entity ks k -> Either String (Entity ks k')
app' f g = let scF = scope f
               scG = scope g
           in if scF == scG
                then Right $ app'' f g
                else Left  $ "can't apply " ++
                             show f ++ " (" ++ show scF ++ ") to " ++
                             show g ++ " (" ++ show scG ++ ")"

  where

    app'' :: Entity ks ('LAM k k') -> Entity ks k -> Entity ks k'
    app'' (Lam e) g' = subst pE g' e -- beta reduction
    app'' f'      g' = App f' g'

app :: Entity ks ('LAM k k') -> Entity ks k -> Entity ks k'
app f g = fromRight $ app' f g

tailSC :: Scope (k ': ks) -> Scope ks
tailSC (Cons s) = scope s

headSC :: Scope (k ': ks) -> Sig ks k
headSC (Cons s) = s

lengthSC :: Scope ks -> Natural
lengthSC Empty    = 0
lengthSC (Cons s) = 1 + lengthSC (scope s)

class Insertable (ls :: [Kind]) where

    insertSC :: Proxy ls ->
                Sig ks k -> Scope  (ls :++ ks)   -> Scope  (ls :++ k ': ks)

    insertS  :: Proxy ls ->
                Sig ks k -> Sig    (ls :++ ks) l -> Sig    (ls :++ k ': ks) l

    insert   :: Proxy ls ->
                Sig ks k -> Entity (ls :++ ks) l -> Entity (ls :++ k ': ks) l

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
    insertS _ (s :: Sig ks k) (LamS (t :: Sig (m ': l ': ls :++ ks) m'))
                           = LamS (insertS (Proxy :: Proxy (m ': l ': ls)) s t)

    insert _ s (Var t)   = Var (insertS (Proxy :: Proxy ls) s t) 
    insert _ s (Lft t e) = let p = Proxy :: Proxy ls
                           in  Lft (insertS p s t) (insert p s e)
    insert _ (s :: Sig ks k) (Lam (e :: Entity (m ': l ': ls :++ ks) m'))
                         = Lam (insert (Proxy :: Proxy (m ': l ': ls)) s e)
    insert p s (App f e) = App (insert p s f) (insert p s e)

class Substitutable (ls :: [Kind]) where

    substSC :: Proxy ls ->
               Entity ks k -> Scope  (ls :++ k ': ks)    -> Scope  (ls :++ ks)

    substS  :: Proxy ls ->
               Entity ks k -> Sig    (ls :++ k ': ks) l' -> Sig    (ls :++ ks) l'

    subst   :: Proxy ls ->
               Entity ks k -> Entity (ls :++ k ': ks) l' -> Entity (ls :++ ks) l'

instance Substitutable '[] where

    substSC _ _ = tailSC

    substS p e (ObjS sc)  = ObjS (substSC p e sc) 
    substS p e (MorS x y) = MorS (subst p e x) (subst p e y)
    substS p e (PrfS f g) = PrfS (subst p e f) (subst p e g)
    substS _ e (LamS (t :: Sig (k ': (k' ': ks)) l))
                          = LamS (substS (Proxy :: Proxy '[k]) e t)

    subst _ e (Var _)   = e 
    subst _ _ (Lft _ f) = f
    subst _ e (Lam (f :: Entity (k ': (k' ': ks)) l))
                        = lam (subst (Proxy :: Proxy '[k]) e f)
    subst p e (App f g) = app (subst p e f) (subst p e g)

instance Substitutable ls => Substitutable (l ': ls) where

    substSC _ e sc = Cons $ substS (Proxy :: Proxy ls) e $ headSC sc

    substS p e (ObjS sc)  = ObjS (substSC p e sc)
    substS p e (MorS x y) = MorS (subst p e x) (subst p e y)
    substS p e (PrfS f g) = PrfS (subst p e f) (subst p e g)
    substS _ (e :: Entity ks k') (LamS (t :: Sig (k ': l ': ls :++ k' ': ks) m))
                          = LamS $ substS (Proxy :: Proxy (k ': l ': ls)) e t

    subst _ e (Var s)   = Var $ substS (Proxy :: Proxy ls) e s
    subst _ e (Lft s f) = let p = Proxy :: Proxy ls
                          in  Lft (substS p e s) (subst p e f)
    subst _ (e :: Entity ks k') (Lam (f :: Entity (k ': (l ': ls :++ k' ': ks)) m))
                        = lam $ subst (Proxy :: Proxy (k ': (l ': ls))) e f
    subst p e (App f g) = app (subst p e f) (subst p e g)

pE :: Proxy ('[] :: [Kind])
pE = Proxy
