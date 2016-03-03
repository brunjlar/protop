{-# LANGUAGE ScopedTypeVariables #-}

module Socrates.Core
    ( MonadSocrates(..)
    , oracle
    ) where

class Monad m => MonadSocrates m where

    question :: String -> m ()

    answer   :: String -> m ()

    oracle'  :: (Show a, Read a) => [a] -> m (Maybe a)

oracle :: (MonadSocrates m, Show a, Read a) => [a] -> m (Maybe a)
oracle []  = return Nothing
oracle [x] = return $ Just x
oracle xs  = oracle' xs
