{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Protop.Logic.NewBuilder
    ( M
    , evalM
    , return
    , (>>=)
    , (>>)
    , popM
    , lftM
    , varM
    , objM
    , morM
    -- , pushM
    ) where

import           Data.Typeable       (Typeable, eqT, (:~:)(..))
import           Prelude hiding      (return, (>>=), (>>), fail)
import qualified Protop.IndexedState as I
import           Protop.Logic.Types

newtype M ks ks' a = M { runM :: I.IState (Scope ks) (Scope ks') a }
    deriving Functor

evalM :: M '[] '[] a -> a
evalM m = I.evalIState (runM m) Empty

return :: a -> M ks ks a
return = M . I.return

infixl 1 >>=
(>>=) :: M ks ks' a -> (a -> M ks' ks'' b) -> M ks ks'' b
m >>= f = M $ runM m I.>>= runM . f

infixl 1 >>
(>>) :: M ks ks' a -> M ks' ks'' b -> M ks ks'' b
m >> n = m >>= const n

get :: M ks ks (Scope ks)
get = M I.get

put :: Scope ks' -> M ks ks' ()
put = M . I.put

modify :: (Scope ks -> Scope ks') -> M ks ks' ()
modify = M . I.modify

pushM :: Sig k ks -> M ks (k ': ks) (Entity k (k ': ks))
pushM s = put (Cons s) >> (return $ var s)

popM :: M (k ': ks) ks ()
popM = get >>= \sc ->
       case sc of Cons s -> put $ scope s

lftM :: forall (a  :: Kind -> [Kind] -> *)
               (l  :: Kind)
               (ls :: [Kind])
               (ks :: [Kind]).
        ( Liftable (a l)
        , HasScope (a l)
        , Show (a l ls)
        , Typeable ls
        , Lifting ks
        ) => a l ls -> M ks ks (a l ks)
lftM x = get >>= \sc ->
         case lftM_ sc x of
            Just x' -> return x'
            Nothing -> error $ "can't lift " ++ show x ++ " from scope " ++ show (scope x) ++
                               " to scope " ++ show sc

varM :: Sig k ks -> M ks (k ': ks) (Entity k (k ': ks))
varM s = pushM s >> (return $ var s)

objM :: M ks ks (Sig 'OBJ ks)
objM = get >>= \sc -> return (objS sc)

morM :: ( Typeable ls
        , Typeable ls'
        , Lifting ks
        ) => Entity 'OBJ ls -> Entity 'OBJ ls' -> M ks ks (Sig 'MOR ks)
morM x y = lftM x >>= \x' ->
           lftM y >>= \y' ->
           return (morS x' y')

{-
lftM :: forall a k ks ls.
        ( Liftable a
        , HasScope (a k)
        , LiftableM ls
        ) => Proxy ls -> a k ks -> STM (ls :++ ks) (ls :++ ks) (a k (ls :++ ks))
lftM p x = get >>= \st -> return $ lftM_ p st x

objM :: STM ks ks (Sig 'OBJ ks)
objM = objS . scope <$> get

varM :: forall k ks. Typeable k => String -> STM ks ks (Entity k ks)
varM n = get >>= \st ->
         case st of
            EmptyST         -> error $ "unknown variable " ++ n
            ConsST n' (s :: Sig k' ks') st'
                | n == n'   -> case (eqT :: Maybe (k :~: k')) of
                                    Just Refl -> return $ var s
                                    Nothing   -> error $ "variable " ++ n ++ " :: " ++ show s ++ " has the wrong kind"
                | otherwise -> put st' >>
                               varM n >>= \x ->
                               put st >>
                               lftM (Proxy :: Proxy '[k']) x

class LiftableM (ks :: [Kind]) where

    lftM_ :: ( Liftable a
             , HasScope (a l)
             ) => Proxy ks -> ST (ks :++ ls) -> a l ls -> a l (ks :++ ls)

instance LiftableM '[] where

    lftM_ _ st x
        | scope st == scope x = x
        | otherwise           = error "incompatible scopes"

instance forall k ks. LiftableM ks => LiftableM (k ': ks) where

    lftM_ _ (ConsST _
                  (s  :: Sig k (ks :++ ls))
                  (st :: ST    (ks :++ ls)))
                  (x  :: a   l         ls)   = lft s $ lftM_ (Proxy :: Proxy ks) st x
    lftM_ _ _ _                              = error "impossible branch"
-}

class Lifting (ks :: [Kind]) where

    lftM_ :: forall (a :: Kind -> [Kind] -> *)
                    (l :: Kind)
                    (ls :: [Kind]).
             ( Liftable (a l)
             , HasScope (a l)
             , Typeable ls
             ) => Scope ks -> a l ls -> Maybe (a l ks)

instance Lifting '[] where

    lftM_ Empty (x :: a l ls) =
        case eqT :: Maybe (ls :~: '[]) of
            Just Refl -> Just x
            Nothing   -> Nothing

instance ( Typeable k
         , Typeable ks
         , Lifting ks) => Lifting (k ': ks) where

    lftM_ (Cons s) (x :: a l ls) =
        case eqT :: Maybe (ls :~: (k ': ks)) of
            Just Refl -> if scope x == (Cons s) then Just x else Nothing
            Nothing   -> case lftM_ (scope s) x of
                            Just x' -> Just $ lft s x'
                            Nothing -> Nothing
