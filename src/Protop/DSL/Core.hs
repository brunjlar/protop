module Protop.DSL.Core
    ( Kind (..)
    , Sig (Obj, Mor)
    , Exp (Var, Id)
    , sig
    , DSLException (..)
    , source
    , target
    , lhs
    , rhs
    , prf
    , (.)
    ) where

import Control.Exception
import Control.Monad.Except (MonadError (..))

import Prelude              hiding ((.))

data Kind =
      OBJ
    | MOR
    | PRF
    deriving (Show, Eq)

data Sig :: Kind -> * where
    Obj :: Sig 'OBJ
    Mor :: Exp 'OBJ -> Exp 'OBJ -> Sig 'MOR
    Prf :: Exp 'MOR -> Exp 'MOR -> Sig 'PRF

instance Show (Sig k) where

    show Obj       = "Obj"
    show (Mor x y) = "(" ++ show x ++ " -> " ++ show y ++ ")"
    show (Prf f g) = "(" ++ show f ++ " == " ++ show g ++ ")"

instance Eq (Sig k) where

    Obj     == Obj       = True
    Mor x y == Mor x' y' = x == x' && y == y'
    Prf f g == Prf f' g' = f == f' && g == g'

data Exp :: Kind -> * where
    Var  :: String -> Sig k -> Exp k
    Id   :: Exp 'OBJ -> Exp 'MOR
    Comp :: Exp 'MOR -> Exp 'MOR -> Exp 'MOR

instance Show (Exp k) where

    show (Var n _)  = n
    show (Id x)     = "id[" ++ show x ++ "]"
    show (Comp f g) = "(" ++ show f ++ " . " ++ show g ++ ")"

instance Eq (Exp k) where

    Var n s  == Var n' s'  = n == n' && s == s'
    Var _ _  == _          = False
    Id x     == Id x'      = x == x'
    Id _     == _          = False
    Comp f g == Comp f' g' = f == f' && g == g'
    Comp _ _ == _          = False

sig :: Exp k -> Sig k
sig (Var _ s)  = s
sig (Id x)     = Mor x x
sig (Comp f g) =
    let (Mor x _) = sig g
        (Mor _ y) = sig f
    in  Mor x y

data DSLException =
    ExpectedEqualObjects (Exp 'OBJ) (Exp 'OBJ)
    deriving (Show, Eq)

instance Exception DSLException

source :: Exp 'MOR -> Exp 'OBJ
source f = case sig f of Mor x _ -> x

target :: Exp 'MOR -> Exp 'OBJ
target f = case sig f of Mor _ x -> x

lhs :: Exp 'PRF -> Exp 'MOR
lhs p = case sig p of Prf f _ -> f

rhs :: Exp 'PRF -> Exp 'MOR
rhs p = case sig p of Prf _ f -> f

prf :: MonadError DSLException m => Exp 'MOR -> Exp 'MOR -> m (Sig 'PRF)
prf f g =
    let sf = source f
        sg = source g
        tf = target f
        tg = target g
    in  if sf /= sg then throwError $ ExpectedEqualObjects sf sg
                    else if tf /= tg then throwError $ ExpectedEqualObjects tf tg
                                     else return $ Prf f g

infixr 9 .

(.) :: MonadError DSLException m => Exp 'MOR -> Exp 'MOR -> m (Exp 'MOR)
f . g =
    let sf = source f
        tg = target g
    in  if sf == tg then return $ Comp f g
                    else throwError $ ExpectedEqualObjects sf tg
