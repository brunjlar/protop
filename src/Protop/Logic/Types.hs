{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module Protop.Logic.Types
    ( Kind(..)
    , Scope(..)
    , headSC
    , tailSC
    , lengthSC
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
    , ScopeM(..)
    , Model
    , compile
    ) where

import Data.List       (intercalate)
import Numeric.Natural (Natural)
import Data.Proxy      (Proxy(..))
import Protop.Core     (Object, MORPHISM, PROOF)
import Protop.Utility  ((:++), fromRight)

data Kind =
    OBJ
  | MOR
  | PRF
  | LAM Kind Kind deriving (Show, Eq)

data Scope :: [Kind] -> * where

    Empty :: Scope '[]

    Cons :: Sig k ks -> Scope (k ': ks)

data Sig :: Kind -> [Kind] -> * where

    ObjS :: Scope ks -> Sig 'OBJ ks

    MorS :: Entity 'OBJ ks -> Entity 'OBJ ks -> Sig 'MOR ks 

    PrfS :: Entity 'MOR ks -> Entity 'MOR ks -> Sig 'PRF ks 

    LamS :: Sig k' (k ': ks) -> Sig ('LAM k k') ks

data Entity :: Kind -> [Kind] -> * where

    Var :: Sig k ks -> Entity k (k ': ks)

    Lft :: Sig k ks -> Entity k' ks -> Entity k' (k ': ks)

    Lam :: Entity k' (k ': ks) -> Entity ('LAM k k') ks

    App :: Entity ('LAM k k') ks -> Entity k ks -> Entity k' ks 

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

class HasScope (a :: Kind -> [Kind] -> *) where

    scope :: a k ks -> Scope ks

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

class Liftable (a :: Kind -> [Kind] -> *) where

    lft_ :: Sig k ks -> a k' ks -> a k' (k ': ks)

instance Liftable Sig where

    lft_ = insertS pE

instance Liftable Entity where

    lft_ = insert pE

lft' :: ( Show (a k' ks)
        , HasScope a
        , Liftable a
        ) => Sig k ks -> a k' ks -> Either String (a k' (k ': ks))
lft' s x = let ss = scope s
               sx = scope x
           in if ss == sx
                then Right $ lft_ s x
                else Left  $ "can't lift " ++ show x ++ " (" ++ show sx ++
                             ") to " ++ show s ++ " (" ++ show ss ++ ")"

lft :: ( Show (a k' ks)
       , HasScope a
       , Liftable a
       ) => Sig k ks -> a k' ks -> a k' (k ': ks)
lft s x = fromRight $ lft' s x

sig :: Entity k ks -> Sig k ks
sig (Var s)   = lft s s
sig (Lft s e) = lft s $ sig e
sig (Lam s)   = LamS (sig s)
sig (App f e) = case sig f of LamS s -> substS pE e s 

show' :: Entity k ks -> String
show' e = show e ++ " :: " ++ show (sig e)

objS :: Scope ks -> Sig 'OBJ ks
objS = ObjS

morS' :: Entity 'OBJ ks -> Entity 'OBJ ks -> Either String (Sig 'MOR ks)
morS' x y = let scX = scope x
                scY = scope y
            in  if scX == scY
                    then Right $ MorS x y
                    else Left  $ "can't make morphism signature from objects " ++
                                 show x ++ " (" ++ show scX ++ ") and " ++
                                 show y ++ " (" ++ show scY ++ ")"

morS :: Entity 'OBJ ks -> Entity 'OBJ ks -> Sig 'MOR ks
morS x y = fromRight $ morS' x y

prfS' :: Entity 'MOR ks -> Entity 'MOR ks -> Either String (Sig 'PRF ks)
prfS' f g = let scF = scope f
                scG = scope g
            in if scF == scG && sig f == sig g
                then Right $ PrfS f g
                else Left  $ "can't make proof signature from morphisms " ++
                             show f ++ " (" ++ show scF ++ ") and " ++
                             show g ++ " (" ++ show scG ++ ")"

prfS :: Entity 'MOR ks -> Entity 'MOR ks -> Sig 'PRF ks
prfS f g = fromRight $ prfS' f g

lamS :: Sig k' (k ': ks) -> Sig ('LAM k k') ks 
lamS = LamS

var :: Sig k ks -> Entity k (k ': ks)
var = Var

lam :: forall k k' ks. Entity k' (k ': ks) -> Entity ('LAM k k') ks 
lam (App (Lft _ e) (Var _)) = e     -- eta reduction
lam e                       = Lam e

app' :: Entity ('LAM k k') ks -> Entity k ks -> Either String (Entity k' ks)
app' f g = let scF = scope f
               scG = scope g
           in if scF == scG
                then Right $ app'' f g
                else Left  $ "can't apply " ++
                             show f ++ " (" ++ show scF ++ ") to " ++
                             show g ++ " (" ++ show scG ++ ")"

  where

    app'' :: Entity ('LAM k k') ks -> Entity k ks -> Entity k' ks
    app'' (Lam e) g' = subst pE g' e -- beta reduction
    app'' f'      g' = App f' g'

app :: Entity ('LAM k k') ks -> Entity k ks -> Entity k' ks
app f g = fromRight $ app' f g

tailSC :: Scope (k ': ks) -> Scope ks
tailSC (Cons s) = scope s

headSC :: Scope (k ': ks) -> Sig k ks
headSC (Cons s) = s

lengthSC :: Scope ks -> Natural
lengthSC Empty    = 0
lengthSC (Cons s) = 1 + lengthSC (scope s)

type family Model (a :: Kind) where
    Model 'OBJ        = Object
    Model 'MOR        = MORPHISM
    Model 'PRF        = PROOF
    Model ('LAM k k') = Model k -> Model k'

data ScopeM (ks :: [Kind]) :: * where

    EmptyM :: ScopeM '[]

    ConsM :: Model k -> ScopeM ks -> ScopeM (k ': ks)

compile :: Entity k ks -> ScopeM ks -> Model k
compile (Var _)   (ConsM e _)  = e
compile (Lft _ e) (ConsM _ sc) = compile e sc
compile (App f g) sc           = compile f sc (compile g sc)
compile (Lam e)   sc           = \e' -> compile e (ConsM e' sc)
compile _         _            = error "impossible branch"

class Insertable (ls :: [Kind]) where

    insertSC :: Proxy ls ->
                Sig k ks -> Scope    (ls :++ ks) -> Scope    (ls :++ k ': ks)

    insertS  :: Proxy ls ->
                Sig k ks -> Sig    l (ls :++ ks) -> Sig    l (ls :++ k ': ks)

    insert   :: Proxy ls ->
                Sig k ks -> Entity l (ls :++ ks) -> Entity l (ls :++ k ': ks)

instance Insertable '[] where

    insertSC _ s _ = Cons s

    insertS _ s (ObjS sc)  = ObjS (insertSC pE s sc)
    
    insertS _ s (MorS x y) = MorS (insert pE s x) (insert pE s y)
    insertS _ s (PrfS f g) = PrfS (insert pE s f) (insert pE s g)
    insertS _ s (LamS (t :: Sig l (k ': ks)))
                           = LamS (insertS (Proxy :: Proxy '[k]) s t)

    insert _ s (Var t)   = Lft s (Var t)
    insert _ s (Lft t e) = Lft s (Lft t e)
    insert _ s (Lam (e :: Entity l (k ': ks)))
                         = Lam (insert (Proxy :: Proxy '[k]) s e)
    insert _ s (App f e) = App (insert pE s f) (insert pE s e)

instance Insertable ls => Insertable (l ': ls) where

    insertSC _ s sc = Cons $ insertS (Proxy :: Proxy ls) s $ headSC sc

    insertS p s (ObjS sc)  = ObjS (insertSC p s sc)
    insertS p s (MorS x y) = MorS (insert p s x) (insert p s y)
    insertS p s (PrfS f g) = PrfS (insert p s f) (insert p s g)
    insertS _ (s :: Sig k ks) (LamS (t :: Sig m' (m ': l ': ls :++ ks)))
                           = LamS (insertS (Proxy :: Proxy (m ': l ': ls)) s t)

    insert _ s (Var t)   = Var (insertS (Proxy :: Proxy ls) s t) 
    insert _ s (Lft t e) = let p = Proxy :: Proxy ls
                           in  Lft (insertS p s t) (insert p s e)
    insert _ (s :: Sig k ks) (Lam (e :: Entity m' (m ': l ': ls :++ ks)))
                         = Lam (insert (Proxy :: Proxy (m ': l ': ls)) s e)
    insert p s (App f e) = App (insert p s f) (insert p s e)

class Substitutable (ls :: [Kind]) where

    substSC :: Proxy ls ->
               Entity k ks -> Scope     (ls :++ k ': ks) -> Scope     (ls :++ ks)

    substS  :: Proxy ls ->
               Entity k ks -> Sig    l' (ls :++ k ': ks) -> Sig    l' (ls :++ ks)

    subst   :: Proxy ls ->
               Entity k ks -> Entity l' (ls :++ k ': ks) -> Entity l' (ls :++ ks)

instance Substitutable '[] where

    substSC _ _ = tailSC

    substS p e (ObjS sc)  = ObjS (substSC p e sc) 
    substS p e (MorS x y) = MorS (subst p e x) (subst p e y)
    substS p e (PrfS f g) = PrfS (subst p e f) (subst p e g)
    substS _ e (LamS (t :: Sig l (k ': (k' ': ks))))
                          = LamS (substS (Proxy :: Proxy '[k]) e t)

    subst _ e (Var _)   = e 
    subst _ _ (Lft _ f) = f
    subst _ e (Lam (f :: Entity l (k ': (k' ': ks))))
                        = lam (subst (Proxy :: Proxy '[k]) e f)
    subst p e (App f g) = app (subst p e f) (subst p e g)

instance Substitutable ls => Substitutable (l ': ls) where

    substSC _ e sc = Cons $ substS (Proxy :: Proxy ls) e $ headSC sc

    substS p e (ObjS sc)  = ObjS (substSC p e sc)
    substS p e (MorS x y) = MorS (subst p e x) (subst p e y)
    substS p e (PrfS f g) = PrfS (subst p e f) (subst p e g)
    substS _ (e :: Entity k' ks) (LamS (t :: Sig m (k ': l ': ls :++ k' ': ks)))
                          = LamS $ substS (Proxy :: Proxy (k ': l ': ls)) e t

    subst _ e (Var s)   = Var $ substS (Proxy :: Proxy ls) e s
    subst _ e (Lft s f) = let p = Proxy :: Proxy ls
                          in  Lft (substS p e s) (subst p e f)
    subst _ (e :: Entity k' ks) (Lam (f :: Entity m (k ': (l ': ls :++ k' ': ks))))
                        = lam $ subst (Proxy :: Proxy (k ': (l ': ls))) e f
    subst p e (App f g) = app (subst p e f) (subst p e g)

pE :: Proxy ('[] :: [Kind])
pE = Proxy
