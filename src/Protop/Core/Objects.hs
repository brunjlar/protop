-- | This module defines /objects/ as instances of the typeclass
-- 'IsObject'. Basically, an object is just a type with an associated
-- /setoid/ (i.e. an instance of 'IsSetoid').
module Protop.Core.Objects
    ( IsObject(..)
    , Object(..)
    ) where

import Data.Function         (on)
import Data.Typeable         (Typeable)
import Protop.Core.Setoids
import Protop.Core.Singleton

class ( Show x
      , Typeable x
      , IsSetoid (Domain x)
      , Singleton x
      ) => IsObject x where

    type Domain x

data Object :: * where
    Object :: IsObject x => x -> Object

instance Show Object where

    show (Object x) = show x

instance Eq Object where

    (==) = (==) `on` show

instance Ord Object where

    compare = compare `on` show
