{-# LANGUAGE ScopedTypeVariables #-}

module Protop.Logic.Socrates.Dialog
    ( socrates
    ) where

import Protop.Logic.Simple
import Protop.Logic.Socrates.Types

socrates :: forall m. MonadSocrates m => m (Maybe (Either Sig Entity))
socrates = do
    question "Signature or Entity"
    mse <- loop
    case mse of
      Nothing        -> answer "ABORT" >> return Nothing
      Just (Left s)  -> answer ("signature: " ++ show s) >> return mse
      Just (Right e) -> answer ("entity: " ++ show' e) >> return mse

  where

    loop :: m (Maybe (Either Sig Entity))
    loop = do
        mx <- oracle [SIG, ENTITY]
        case mx of
          Nothing     -> return Nothing
          Just SIG    -> getSig    >>= maybe loop (return . Just . Left)
          Just ENTITY -> do
              ms <- getSig
              case ms of
                Nothing -> answer "ABORT" >> loop
                Just s  -> do
                    me <- getEntity s
                    case me of
                      Nothing -> answer "ABORT" >> loop
                      Just e  -> return $ Just $ Right e

getSig :: MonadSocrates m => m (Maybe Sig)
getSig = do
    question "Signature"
    let s = objS empty
    answer $ show s
    return $ Just s

getEntity :: forall m. MonadSocrates m => Sig -> m (Maybe Entity)
getEntity s = do
    question $ "Entity for signature " ++ show s
    me <- loop
    case me of
      Nothing -> answer "ABORT" >> return Nothing
      Just e  -> answer (show' e) >> return (Just e)

  where

    loop :: m (Maybe Entity)
    loop = return $ Just $ var $ objS empty

data SigOrEntity = SIG | ENTITY deriving (Show, Read, Eq)
