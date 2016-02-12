{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Protop.Core.Natural
    ( N(..)
    , Zero(..)
    , Succ(..)
    , Rec(..)
    , RECZ(..)
    , RECS(..)
    , REC(..)
    , Add
    , add
    , Mul
    , mul
    ) where

import Data.Proxy                 (Proxy(..))
import Numeric.Natural            (Natural)
import Protop.Core.Compositions
import Protop.Core.Exponentials
import Protop.Core.Morphisms
import Protop.Core.Objects
import Protop.Core.Products
import Protop.Core.Proofs
import Protop.Core.Setoids
import Protop.Core.Symmetries
import Protop.Core.Terminal
import Protop.Core.Transitivities

data N = N

instance Show N where

    show N = "N"

instance IsObject N where

    type Domain N = Natural
    proxy _ = N

data Zero = Zero

instance Show Zero where

    show Zero = "Zero"

instance IsMorphism Zero where

    type Source Zero = T
    type Target Zero = N
    onDomains _ = setZero
    proxy' _    = Zero

data Succ = Succ

instance Show Succ where

    show Succ = "Succ"

instance IsMorphism Succ where

    type Source Succ = N
    type Target Succ = N

    onDomains _ = setSucc
    proxy' _    = Succ

type CRec z s = ( IsMorphism z
                , IsMorphism s
                , Source z ~ T
                , Target z ~ Source s
                , Target s ~ Source s
                )

data Rec :: * -> * -> * where
    Rec :: CRec z s => z -> s -> Rec z s

instance Show (Rec z s) where

    show (Rec z s) = "(Rec " ++ show z ++ " " ++ show s ++ ")"

instance CRec z s => IsMorphism (Rec z s) where

    type Source (Rec z s) = N
    type Target (Rec z s) = Target z

    onDomains (Rec z s) = setRec (z .$ star) (onDomains s)
    proxy' _ = Rec (proxy' Proxy) (proxy' Proxy)

data RECZ :: * -> * -> * where
    RECZ :: CRec z s => z -> s -> RECZ z s

instance Show (RECZ z s) where

    show (RECZ z s) = "(RECZ " ++ show z ++ " " ++ show s ++ ")"

instance CRec z s => IsProof (RECZ z s) where

    type Lhs (RECZ z s) = Rec z s :. Zero
    type Rhs (RECZ z s) = z

    proof (RECZ z _) _ = reflexivity $ z .$ star
    proxy'' _          = RECZ (proxy' Proxy) (proxy' Proxy)

data RECS :: * -> * -> * where
    RECS :: CRec z s => z -> s -> RECS z s

instance Show (RECS z s) where

    show (RECS z s) = "(RECN " ++ show z ++ " " ++ show s ++ ")"

instance CRec z s => IsProof (RECS z s) where

    type Lhs (RECS z s) = Rec z s :. Succ 
    type Rhs (RECS z s) = s :. Rec z s 

    proof (RECS z s) n = reflexivity $ s :. Rec z s .$ n
    proxy'' _          = RECS (proxy' Proxy) (proxy' Proxy)

type CREC z s f pz ps = ( CRec z s
                        , IsMorphism f
                        , IsProof pz
                        , IsProof ps
                        , Source s ~ N
                        , Target f ~ Target z
                        , Lhs pz ~ (f :. Zero)
                        , Rhs pz ~ z
                        , Lhs ps ~ (f :. Succ)
                        , Rhs ps ~ (s :. f)
                        )

data REC :: * -> * -> * -> * -> * -> * where
    REC :: CREC z s f pz ps => z -> s -> f -> pz -> ps -> REC z s f pz ps

instance Show (REC z s f pz ps) where

    show (REC z s f pz ps) = 
        "(REC " ++ show z ++ " " ++ show s ++ " " ++ show f ++ " " ++ show pz ++ " " ++ show ps ++ ")"

instance CREC z s f pz ps => IsProof (REC z s f pz ps) where

    type Lhs (REC z s f pz ps) = f
    type Rhs (REC z s f pz ps) = Rec z s

    proof (REC z s _ pz ps) n = loop 0 $ proof (pz :> SYMM (RECZ z s)) star 

      where

        loop :: Natural -> Proofs (DTarget z) -> PTarget z
        loop n' p | n == n'   = p
                  | otherwise = loop (succ n') p'

          where

            pr :: Proxy (DTarget z)
            pr = Proxy

            p', p1, p2, p3 :: PTarget z
            p' = transitivity pr p1 $ transitivity pr p2 p3
            
            p1 = proof ps n'
            p2 = (onProofs $ onDomains s) p
            p3 = proof (SYMM $ RECS z s) n' 

    proxy'' _ = REC (proxy' Proxy) (proxy' Proxy) (proxy' Proxy) (proxy'' Proxy) (proxy'' Proxy)

type Add = Uncurry
            (Rec
                (Curry T N (Pr2 T N))
                (Curry (N :-> N) N (Succ :. Eval N N)))
            N
            N
                
add :: Morphism (N :* N) N
add = Morphism $ proxy' (Proxy :: Proxy Add)

type Mul = Uncurry
            (Rec
                (Curry T N (Zero :. Pr1 T N))
                (Curry (N :-> N) N (Add :. (Eval N N :&&& Pr2 (N :-> N) N))))
            N
            N

mul :: Morphism (N :* N) N
mul = Morphism $ proxy' (Proxy :: Proxy Mul)
