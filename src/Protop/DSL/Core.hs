module Protop.DSL.Core
    ( Kind (..)
    , SigE (Obj, Mor, Lam, Sgm) 
    , Sig
    , Exp (Var, Pr1, Pr2)
    , source
    , target
    , lhs
    , rhs
    , DSLException (..)
    , prf
    ) where

import           Control.Exception
import           Control.Monad.Except (MonadError (..))

import Protop.DSL.Expression
import Protop.DSL.Kind
import Protop.DSL.Signature

type Sig k = SigE Exp k

data DSLException where
    DistinctSignatures :: Sig k -> Sig k -> DSLException

deriving instance Show DSLException

instance Eq DSLException where

    DistinctSignatures s t == DistinctSignatures s' t' = compareK s s' == EQ && compareK t t' == EQ

instance Exception DSLException

source :: Exp MOR -> Exp OBJ
source f = case sig f of Mor x _ -> x

target :: Exp MOR -> Exp OBJ
target f = case sig f of Mor _ x -> x

lhs :: Exp PRF -> Exp MOR
lhs p = case sig p of Prf f _ -> f

rhs :: Exp PRF -> Exp MOR
rhs p = case sig p of Prf _ f -> f

prf :: MonadError DSLException m => Exp MOR -> Exp MOR -> m (Sig PRF)
prf f g = case compareK (sig f) (sig g) of
    EQ -> return $ Prf f g
    _  -> throwError $ DistinctSignatures (sig f) (sig g) 
