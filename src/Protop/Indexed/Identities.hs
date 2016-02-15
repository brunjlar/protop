{-# LANGUAGE DataKinds #-}

module Protop.Indexed.Identities
    ( morId
    ) where

import Protop.Core
import Protop.Indexed.Types

morId :: Entity' 0 ('LAM 'OBJ 'MOR)
morId = let v = var objS
        in  axiomLam "id" objS (morS v v) $
            \x -> case toObject x of Object x' -> axiomMor $ Id x'

