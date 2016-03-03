{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Socrates.Script
    ( SocratesScript
    , runSocratesScript
    ) where

import qualified Control.Monad.State         as S
import           Socrates.Core

newtype SocratesScript a = SocratesScript (S.State [String] a)
    deriving (Functor, Applicative, Monad, S.MonadState [String])

runSocratesScript :: SocratesScript a -> [String] -> a
runSocratesScript (SocratesScript s) = S.evalState s

instance MonadSocrates SocratesScript where

    oracle' _ = do
        (x : xs) <- S.get
        S.put xs
        return $ Just $ read x

    question  = const $ return ()

    answer    = const $ return ()
