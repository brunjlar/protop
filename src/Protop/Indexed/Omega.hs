{-# LANGUAGE DataKinds #-}

module Protop.Indexed.Omega
    ( objO
    , morTrue
    ) where

import Protop.Core
import Protop.Indexed.Types

objO :: Entity' 0 'OBJ
objO = axiomObj O

morTrue :: Entity' 0 'MOR
morTrue = axiomMor True'
