{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Protop.Logic.NewBuilder
    ( STM
    , evalSTM
    , objSM
    ) where

import           Data.List           (intercalate)
import           Prelude hiding      (return, (>>=), (>>), fail)
import qualified Protop.IndexedState as I
import           Protop.Logic.Types

data ST :: [Kind] -> * where

    EmptyST :: ST '[]

    ConsST  :: String -> Sig k ks -> ST ks -> ST (k ': ks)

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

consST :: String -> Sig k ks -> ST ks -> ST (k ': ks)
consST n s st
    | scope s == scope st = ConsST n s st
    | otherwise           = error $ show s ++ " has scope " ++ show (scope s) ++
                                    ", but state " ++ show st ++ " has scope " ++
                                    show (scope st)

newtype STM ks ks' a = STM { runSTM :: I.IState (ST ks) (ST ks') a }
    deriving Functor

evalSTM :: STM '[] '[] a -> a
evalSTM m = I.evalIState (runSTM m) EmptyST

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

objSM :: STM ks ks (Sig 'OBJ ks)
objSM = objS . scope <$> get

pushM :: String -> Sig k ks -> STM ks (k ': ks) ()
pushM n s = modify $ consST n s

popM :: STM (k ': ks) ks ()
popM = get >>= \st ->
       case st of ConsST _ _ t -> put t
