{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Protop.Logic.Builder
    ( M
    , evalM'
    , evalM
    , popM
    , lftM
    , objM
    , morM
    , prfM
    , lamSM
    , sgmSM
    , varM
    , lamM
    , appM
    , sgmM
    ) where

import qualified Control.Monad.Identity as I
import qualified Control.Monad.State    as S
import           Protop.Logic.Simple

newtype M m a = M { runM :: S.StateT Scope m a } deriving (Functor, Applicative, Monad, S.MonadState Scope)

evalM' :: Monad m => M m a -> m a
evalM' m = do
    (x, sc) <- S.runStateT (runM m) empty
    if sc == empty
       then return x
       else error "scope not empty"

evalM :: M I.Identity a -> a
evalM = I.runIdentity . evalM'

varM :: Monad m => Sig -> M m Entity
varM s = do
    sc <- S.get
    S.when (sc /= scope s) $ fail $ show s ++ " has scope " ++ show (scope s) ++
                                    ", expecting scope " ++ show sc
    S.put $ cons s
    return $ var s

popM :: Monad m => M m ()
popM = do
    sc <- S.get
    case headTail sc of
      Nothing       -> fail "can't pop empty scope"
      Just (_, sc') -> S.put sc'

lftM :: (Monad m, Liftable a, HasScope a, Show a) => a -> M m a
lftM x = do
    sc <- S.get
    return $ lft' sc x

objM :: Monad m => M m Sig
objM = objS <$> S.get

morM :: Monad m => Entity -> Entity -> M m Sig
morM x y = morS <$> lftM x <*> lftM y

prfM :: Monad m => Entity -> Entity -> M m Sig
prfM f g = prfS <$> lftM f <*> lftM g

lamSM :: Monad m => Sig -> M m Sig
lamSM s = do
    s' <- lftM s
    popM
    return $ lamS s'

sgmSM :: Monad m => Sig -> M m Sig
sgmSM s = do
    s' <- lftM s
    popM
    return $ sgmS s'

lamM :: Monad m => Entity -> M m Entity
lamM e = do
    e' <- lftM e
    popM
    return $ lam e'

appM :: Monad m => Entity -> Entity -> M m Entity
appM e f = app <$> lftM e <*> lftM f

sgmM :: Monad m => Sig -> Entity -> Entity -> M m Entity
sgmM s e f = sgm <$> lftM s <*> lftM e <*> lftM f
