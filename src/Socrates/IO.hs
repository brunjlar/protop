{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Socrates.IO
    ( runSocratesIO
    ) where

import           Control.Monad               (forM_)
import qualified Control.Monad.IO.Class      as I
import qualified Control.Monad.State         as S
import           Numeric.Natural
import           Socrates.Core
import           Text.Read                   (readMaybe)

newtype SocratesIO a = SocratesIO (S.StateT Natural IO a)
    deriving (Functor, Applicative, Monad, I.MonadIO, S.MonadState Natural)

runSocratesIO :: Socrates a -> IO (Maybe a)
runSocratesIO s = let (SocratesIO m) = runSocrates s in S.evalStateT m 0

instance MonadSocrates SocratesIO where

    oracle xs = do
        forM_ (zip [1 :: Int ..] xs) $ \(n, x) -> out $ show n ++ " - " ++ show x
        mn <- readMaybe <$> I.liftIO getLine
        return $ case mn of
                     Just n
                         | n >= 1 && n <= length xs -> Just $ fromIntegral $ n - 1
                         | otherwise                -> Nothing
                     Nothing                        -> Nothing

    question s = out s >> S.modify succ

    answer s   = S.modify pred >> out s

out :: String -> SocratesIO ()
out s = do
    n <- S.get
    let pad = replicate (2 * fromIntegral n) ' '
    I.liftIO $ putStrLn $ pad ++ s
