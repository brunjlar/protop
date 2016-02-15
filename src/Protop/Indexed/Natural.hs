{-# LANGUAGE DataKinds #-}

module Protop.Indexed.Natural
    ( objN
    , morZero
    , morSucc
    ) where

import Protop.Core
import Protop.Indexed.Types

objN :: Entity' 0 'OBJ
objN = axiomObj N

morZero, morSucc :: Entity' 0 'MOR
morZero = axiomMor Zero
morSucc = axiomMor Succ
