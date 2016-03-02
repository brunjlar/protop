{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Protop.Logic.Sokrates
    ( MonadSokrates(..)
    , SokratesIO
    , runSokratesIO
    , SokratesScript
    , runSokratesScript
    ) where

import           Control.Monad          (forM_)
import qualified Control.Monad.IO.Class as I
import qualified Control.Monad.State    as S
import           Text.Read              (readMaybe)

class Monad m => MonadSokrates m where

    oracle :: (Show a, Read a) => [a] -> m a

newtype SokratesIO a = SokratesIO { runSokratesIO :: IO a }
    deriving (Functor, Applicative, Monad, I.MonadIO)

instance MonadSokrates SokratesIO where

    oracle xs = do
        forM_ (zip [1 :: Int ..] xs) $ \(n, x) -> I.liftIO $ putStrLn $ show n ++ " - " ++ show x
        mn <- readMaybe <$> I.liftIO getLine
        case mn of
            Just n
                | n >= 1 && n <= length xs -> return $ xs !! (n - 1)
                | otherwise                -> oracle xs
            Nothing                        -> oracle xs

newtype SokratesScript a = SokratesScript (S.State [String] a)
    deriving (Functor, Applicative, Monad, S.MonadState [String])

runSokratesScript :: SokratesScript a -> [String] -> a
runSokratesScript (SokratesScript s) = S.evalState s

instance MonadSokrates SokratesScript where

    oracle _ = do
        (x : xs) <- S.get
        S.put xs
        return $ read x

