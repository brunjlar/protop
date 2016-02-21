{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Protop.Logic.Builder
    ( BuilderT
    , runBuilderT
    , Builder
    , runBuilder
    , objB
    , lamSB
    , addVarB
    , getVarB
    , lftB
    ) where

import           Control.Monad.Identity (Identity(..))
import qualified Control.Monad.State    as S
import           Data.List              (find)
import           Protop.Logic.Simple

data St = St
    { scopes :: [SCOPE]
    , sigs   :: [Maybe SIG]
    , vars   :: [(String, ENTITY)]
    }

initialSt :: St
initialSt = St
    { scopes = [emptySC]
    , sigs   = [Nothing]
    , vars   = []
    }

newtype BuilderT m a = BuilderT (S.StateT St m a)
    deriving (Functor, Applicative, Monad, S.MonadState St, S.MonadTrans)

runBuilderT :: Monad m => BuilderT m a -> m a
runBuilderT (BuilderT mx) = S.evalStateT mx initialSt

type Builder = BuilderT Identity

runBuilder :: Builder a -> a
runBuilder = runIdentity . runBuilderT

pop :: Monad m => BuilderT m ()
pop = do
    st <- S.get
    if scopes st == [emptySC]
        then fail "can't pop emty scope"
        else S.put St
            { scopes = tail $ scopes st
            , sigs   = tail $ sigs st
            , vars   = tail $ vars st
            }

objB :: Monad m => BuilderT m SIG
objB = do
    st <- S.get
    return $ objSIG $ head $ scopes st

lamSB :: Monad m => SIG -> BuilderT m SIG
lamSB s = do
    sc <- S.gets scopes
    if sc == [emptySC]
        then fail "can't create lambda signature in empty scope"
        else do
            let scS = scopeSIG s
            if scS /= head sc
                then fail $ "signature " ++ show s ++ " has scope " ++
                            show scS ++ ", but was expecting scope " ++
                            show (head sc)
                else do
                    pop
                    return $ lamSIG s

addVarB :: Monad m => String -> SIG -> BuilderT m ENTITY
addVarB v s = do
    st <- S.get
    let scS = scopeSIG s
        sc  = head $ scopes st
    if scopeSIG s /= sc
        then fail $ "signature " ++ show s ++ " has scope " ++
                    show scS ++ ", but was expecting scope " ++
                    show sc
        else do
            let e = varE s
            S.put St
                { scopes = scopeE e : scopes st
                , sigs   = Just s   : sigs   st
                , vars   = (v, e)   : vars   st
                }
            return e

getVarB :: Monad m => String -> BuilderT m ENTITY
getVarB v = do
    vs <- S.gets vars
    case find (\(v', _) -> v' == v) vs of
        Just (_, e) -> lftB e
        Nothing     -> fail $ "no variable with name '" ++ v ++ "' in scope"

lftB :: Monad m => ENTITY -> BuilderT m ENTITY
lftB e = do
    st <- S.get
    return $ f $ zip (sigs st) (scopes st) where

    f :: [(Maybe SIG, SCOPE)] -> ENTITY
    f [(_, _)]
        | scopeE e == emptySC = e
        | otherwise           = error $ "can't lift entity " ++ show e ++ " with scope "
                                         ++ show (scopeE e) ++ " into scope"
    f ((Just s, sc) : ss)
        | scopeE e == sc      = e
        | otherwise           = lftE s $ f ss
    f _                       = error "impossible branch"
