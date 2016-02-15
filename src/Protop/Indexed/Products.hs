{-# LANGUAGE DataKinds #-}

module Protop.Indexed.Products
    ( objProd
    ) where

import Protop.Core
import Protop.Indexed.Types

objProd :: Entity' 0 ('LAM 'OBJ ('LAM 'OBJ 'OBJ))
objProd =
    axiomLam "Prod" objS (lamS objS objS) $ \x ->
    axiomLam undefined objS objS          $ \y ->
    case (toObject x, toObject y) of
        (Object x', Object y') -> axiomObj $ x' :* y'
