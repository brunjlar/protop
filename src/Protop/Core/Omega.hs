{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}

module Protop.Core.Omega
    ( OPoint(..)
    , OProof(..)
    , O(..)
    , True'(..)
    , Sub(..)
    , SUB(..)
    , Omega(..)
    , OMEGA(..)
    ) where

import Data.Proxy               (Proxy(..))
import Data.Typeable            ((:~:)(..))
import Protop.Core.Compositions
import Protop.Core.Identities
import Protop.Core.Monos
import Protop.Core.Morphisms
import Protop.Core.Objects
import Protop.Core.Proofs
import Protop.Core.Setoids
import Protop.Core.Terminal
import Protop.Utility

data OPoint :: * where

    OPoint :: IsMorphism f => f -> DTarget f -> OPoint

data OProof :: * where

    OProof :: ( IsMorphism f
              , IsMorphism g
              ) => f -> g -> DTarget f -> DTarget g ->
                   ((DSource f, PTarget f) -> (DSource g, PTarget g)) ->
                   ((DSource g, PTarget g) -> (DSource f, PTarget f)) ->
                   OProof

instance IsSetoid OPoint where

    type Proofs OPoint = OProof

    reflexivity (OPoint f x)               = OProof f f x x id id
    symmetry _ (OProof f g x y i j)        = OProof g f y x j i
    transitivity _ (OProof f  g x _ i  j)
                   (OProof g' h _ z i' j') =
        case eqT' g g' of Refl -> OProof f h x z (i' . i) (j . j')
    setLhs (OProof f _ x _ _ _)            = OPoint f x
    setRhs (OProof _ g _ y _ _)            = OPoint g y

data O = O

instance Show O where

    show O = "O"

instance IsObject O where

    type Domain O = OPoint

    proxy _ = O

data True' = True'

instance Show True' where

    show True' = "true"

instance IsMorphism True' where

    type Source True' = T
    type Target True' = O

    onDomains _ = Functoid (const x) (const px) where
        x  = OPoint (Id T) star
        px = OProof (Id T) (Id T) star star id id

    proxy' _ = True'

data Sub :: * -> * -> * where
   
   Sub :: CMONO f p => f -> p -> Sub f p

instance Show (Sub f p) where

    show (Sub f _) = "(sub " ++ show f ++ ")"

instance CMONO f p => IsMorphism (Sub f p) where

    type Source (Sub f p) = Target f
    type Target (Sub f p) = O

    onDomains (Sub f _) = Functoid s s' where
        s     = OPoint f
        s' px =
            let r = Proxy :: Proxy (DTarget f)
            in  OProof f f (setLhs px) (setRhs px)
                    (\(y, p) -> (y, transitivity r p px))
                    (\(y, p) -> (y, transitivity r p $ symmetry r px))

    proxy' _ = Sub (proxy' Proxy) (proxy'' Proxy)

data SUB :: * -> * -> * where
   
   SUB :: CMONO f p => f -> p -> SUB f p

instance Show (SUB f p) where

    show (SUB f _) = "(SUB " ++ show f ++ ")"

instance CMONO f p => IsProof (SUB f p) where

    type Lhs (SUB f p) = Sub f p :. f
    type Rhs (SUB f p) = True' :. Terminal (Source f)
  
    proof (SUB f _) x = OProof f (Id T) (f .$ x) star
                            (const (star, star))
                            (const (x, reflexivity $ f .$ x))
    proxy'' _         = SUB (proxy' Proxy) (proxy'' Proxy)

type COmega f p g q = ( CMONO f p
                      , IsMorphism g
                      , IsProof q
                      , Target g ~ Target f
                      , Lhs q ~ (Sub f p :. g)
                      , Rhs q ~ (True' :. Terminal (Source g))
                      )

data Omega :: * -> * -> * -> * -> * where

    Omega :: COmega f p g q => f -> p -> g -> q -> Omega f p g q

instance Show (Omega f p g q) where

    show (Omega f _ g _) = "(omega " ++ show f ++ " " ++ show g ++ ")"

lift ::COmega f p g q =>
            f -> q -> DSource g -> (DSource f, PTarget f)
lift f q x =
    case proof q x of
        OProof f' g' _ _ _ j ->
            case (eqT' f f', eqT' (Id T) g') of
                (Refl, Refl) -> j (star, star)

instance COmega f p g q => IsMorphism (Omega f p g q) where

    type Source (Omega f p g q) = Source g
    type Target (Omega f p g q) = Source f

    onDomains (Omega f p g q) = Functoid t t' where
        t   x = fst $ lift' x
        t' px =
            let (y1, p1) = lift' $ setLhs px
                (y2, p2) = lift' $ setRhs px
                r        = Proxy :: Proxy (DTarget f)
                symm     = symmetry r
                trans    = transitivity r
                px'      = onProofs (onDomains g) px
                p'       = trans p1 $ trans px' $ symm p2 
            in  monoIsInjective f p y1 y2 p'

        lift' :: DSource g -> (DSource f, PTarget f)
        lift' = lift f q

    proxy' _ = Omega (proxy' Proxy)
                     (proxy'' Proxy)
                     (proxy' Proxy)
                     (proxy'' Proxy)

data OMEGA :: * -> * -> * -> * -> * where

    OMEGA :: COmega f p g q => f -> p -> g -> q -> OMEGA f p g q

instance Show (OMEGA f p g q) where

    show (OMEGA f p g q) = "(OMEGA " ++ show f ++ " " ++ show p ++ " " ++
                           show g ++ " " ++ show q ++ ")"

instance COmega f p g q => IsProof (OMEGA f p g q) where

    type Lhs (OMEGA f p g q) = f :. Omega f p g q
    type Rhs (OMEGA f p g q) = g

    proof (OMEGA f _ _ q) x = snd $ lift f q x

    proxy'' _ = OMEGA (proxy' Proxy)
                      (proxy'' Proxy)
                      (proxy' Proxy)
                      (proxy'' Proxy)
