module Protop.DSL.Kind
    ( Kind (..)
    , Kinded (..)
    , caseEqK
    , compareK
    , eqK
    , U (..)
    ) where

import Data.Typeable      (Typeable, typeRep, eqT)
import Data.Type.Equality ((:~:) (..))
import Data.Constraint    (Dict (..), withDict)

data Kind =
      OBJ
    | MOR
    | PRF
    | LAM Kind Kind
    | SGM Kind Kind
    deriving (Show, Eq, Typeable)

class Kinded (a :: Kind -> *) where

    typeable :: a k -> Dict (Typeable k)

    show' :: a k -> String

    compare' :: a k -> a k -> Ordering

caseEqK :: forall a b k l. Kinded a 
        => a k 
        -> a l
        -> ((Typeable k, (k ~ l)) => b)
        -> ((Typeable k, Typeable l) => b)
        -> b
caseEqK x y b b' =
    withDict (typeable x) $
    withDict (typeable y) $
    case eqT @k @l of
        Nothing   -> b'
        Just Refl -> b

compareK :: Kinded a => a k -> a l -> Ordering
compareK x y = caseEqK x y (compare' x y) $
    let x' = typeRep x
        y' = typeRep y
    in  compare x' y'

eqK :: Kinded a => a k -> a l -> Bool
eqK x y = compareK x y == EQ

data U (a :: Kind -> *) :: * where
    U :: Kinded a => a k -> U a

instance Show (U a) where

    show (U x) = show' x

instance Eq (U a) where

    U x == U y = eqK x y

instance Ord (U a) where

    compare (U x) (U y) = compareK x y
