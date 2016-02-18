{-# Language ScopedTypeVariables #-}
{-# Language TypeFamilies #-}
{-# Language DataKinds #-}

module Protop.Logic.Model
    ( Model
    ) where

import Protop.Core
import Protop.Logic.Types

type family Model (a :: Kind) where
    Model 'OBJ        = Object
    Model 'MOR        = MORPHISM
    Model 'PRF        = PROOF
    Model ('LAM k k') = Model k -> Model k'
