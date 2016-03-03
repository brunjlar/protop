{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}

module Socrates.Core
    ( MonadSocrates(..)
    , Socrates
    , runSocrates
    , scoped
    , choice
    ) where

import Control.Monad.Operational
import Numeric.Natural

class Monad m => MonadSocrates m where

    question :: String -> m ()

    answer   :: String -> m ()

    oracle   :: Show a => [a] -> m (Maybe Natural)

data Instr :: * -> * where

    Scoped :: String -> (a -> String) -> Socrates a -> Instr a

    Choice :: Show b => [(b, Socrates a)] -> Instr a

newtype Socrates a = Socrates (Program Instr a) deriving (Functor, Applicative, Monad)

runSocrates :: forall m a. MonadSocrates m => Socrates a -> m (Maybe a)
runSocrates (Socrates p) = eval $ view p where

    eval :: ProgramView Instr a -> m (Maybe a)
    eval (Return x)            = return $ Just x
    eval (Scoped s f q :>>= g) = do
        question s
        mx <- runSocrates q
        case mx of
          Nothing -> answer "ABORT" >> return Nothing
          Just x  -> answer (f x)   >> eval (view $ g x)
    eval (Choice xs    :>>= g) =
        case xs of
          []       -> return Nothing
          [(_, q)] -> do
              mx <- runSocrates q
              case mx of
                Nothing -> return Nothing
                Just x  -> eval (view $ g x)
          _        -> do
              mx <- loop
              case mx of
                Nothing -> return Nothing
                Just x  -> eval (view $ g x)

      where

        loop = do
            mi <- oracle $ map fst xs
            case mi of
              Nothing -> return Nothing
              Just i  -> do
                  let q = snd (xs !! fromIntegral i)
                  mx <- runSocrates q
                  case mx of
                    Nothing -> loop
                    Just _  -> return mx

scoped :: String -> (a -> String) -> Socrates a -> Socrates a
scoped s f q = Socrates $ singleton $ Scoped s f q

choice :: Show b => [(b, Socrates a)] -> Socrates a
choice = Socrates . singleton . Choice
