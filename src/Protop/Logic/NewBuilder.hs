{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Protop.Logic.NewBuilder
    ( STM
    , evalM
    , return
    , (>>=)
    , (>>)
    , objM
    , pushM
    , popM
    , varM
    ) where

import           Data.List           (intercalate)
import           Data.Proxy          (Proxy(..))
import           Data.Typeable       (Typeable, eqT, (:~:)(..))
import           Prelude hiding      (return, (>>=), (>>), fail)
import qualified Protop.IndexedState as I
import           Protop.Logic.Types
import           Protop.Utility      ((:++))

data ST :: [Kind] -> * where

    EmptyST :: ST '[]

    ConsST  :: Typeable k => String -> Sig k ks -> ST ks -> ST (k ': ks)

instance HasScope ST where

    scope EmptyST        = Empty
    scope (ConsST _ s _) = Cons s

instance Eq (ST ks) where

    EmptyST      == EmptyST         = True
    ConsST n s t == ConsST n' s' t' = n == n' && s == s' && t == t'
    _            == _               = False

instance Show (ST ks) where

    show EmptyST = "{}"
    show st      = "{" ++ intercalate ", " (f st) ++ "}" where

        f :: ST ks' -> [String]
        f EmptyST = []
        f (ConsST n s t) = (n ++ " :: " ++ show s) : f t

consST :: Typeable k => String -> Sig k ks -> ST ks -> ST (k ': ks)
consST n s st
    | scope s == scope st = ConsST n s st
    | otherwise           = error $ show s ++ " has scope " ++ show (scope s) ++
                                    ", but state " ++ show st ++ " has scope " ++
                                    show (scope st)

newtype STM ks ks' a = STM { runSTM :: I.IState (ST ks) (ST ks') a }
    deriving Functor

evalM :: STM '[] '[] a -> a
evalM m = I.evalIState (runSTM m) EmptyST

return :: a -> STM ks ks a
return = STM . I.return

infixl 1 >>=
(>>=) :: STM ks ks' a -> (a -> STM ks' ks'' b) -> STM ks ks'' b
m >>= f = STM $ runSTM m I.>>= runSTM . f

infixl 1 >>
(>>) :: STM ks ks' a -> STM ks' ks'' b -> STM ks ks'' b
m >> n = m >>= const n

get :: STM ks ks (ST ks)
get = STM I.get

put :: ST ks' -> STM ks ks' ()
put = STM . I.put

modify :: (ST ks -> ST ks') -> STM ks ks' ()
modify = STM . I.modify

pushM :: Typeable k => String -> Sig k ks -> STM ks (k ': ks) ()
pushM n s = modify $ consST n s

popM :: STM (k ': ks) ks ()
popM = get >>= \st ->
       case st of ConsST _ _ t -> put t

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

