{-# LANGUAGE FlexibleInstances #-}

module Protop.IndexedState
    ( IState(..)
    , evalIState
    , execIState
    , return
    , (>>=)
    , (>>)
    , fail
    , join
    , get
    , put
    , modify
    ) where

import Control.Arrow  (first)
import Prelude hiding (return, (>>=), (>>), fail)

newtype IState i o a = IState { runIState :: i -> (a, o) }

evalIState :: IState i o a -> i -> a
evalIState s i = fst $ runIState s i

execIState :: IState i o a -> i -> o
execIState s i = snd $ runIState s i

instance Functor (IState i o) where

    fmap f s = IState $ first f . runIState s

instance Applicative (IState s s) where

    pure = return

    mf <*> mx = mf >>= \f ->
                mx >>= \x ->
                return $ f x

return :: a -> IState s s a
return a = IState $ \s -> (a, s)

infixl 1 >>=
(>>=) :: IState i s a -> (a -> IState s o b) -> IState i o b
ma >>= f = IState $ \i -> let (a, s) = runIState ma i
                          in  runIState (f a) s

infixl 1 >>
(>>) :: IState i s a -> IState s o b -> IState i o b
ma >> mb = ma >>= const mb

fail :: String -> IState i o a
fail = error

join :: IState i s (IState s o a) -> IState i o a
join m = m >>= id

get :: IState s s s
get = IState $ \s -> (s, s)

put :: o -> IState i o ()
put o = IState $ const ((), o)

modify :: (i -> o) -> IState i o ()
modify f = get >>= put . f
