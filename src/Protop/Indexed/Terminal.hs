{-# LANGUAGE DataKinds #-}

module Protop.Indexed.Terminal
    ( objT
    ) where

import Protop.Core
import Protop.Indexed.Types

objT :: Entity' 0 'OBJ
objT = axiomObj T
