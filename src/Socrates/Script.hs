{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Socrates.Script
    ( runSocratesScript
    ) where

import qualified Control.Monad.State as S
import           Numeric.Natural
import           Socrates.Core

newtype SocratesScript a = SocratesScript (S.State [Natural] a)
    deriving (Functor, Applicative, Monad, S.MonadState [Natural])

runSocratesScript :: Socrates a -> [Natural] -> Maybe a
runSocratesScript s = let (SocratesScript m) = runSocrates s in S.evalState m

instance MonadSocrates SocratesScript where

    oracle _ = do
        (x : xs) <- S.get
        S.put xs
        return $ Just $ x - 1

    question  = const $ return ()

    answer    = const $ return ()
