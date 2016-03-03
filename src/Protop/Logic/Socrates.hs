{-# LANGUAGE ScopedTypeVariables #-}

module Protop.Logic.Socrates
    ( socrates
    ) where

import Control.Arrow       ((&&&))
import Protop.Logic.Simple
import Socrates

socrates :: Socrates (Either Sig Entity)
socrates = scoped
    "Sig or Entity"
    (either show show)
    (choice [("Sig", Left <$> socSig empty), ("Entity", Right <$> socEntity empty)])

socSig :: Scope -> Socrates Sig
socSig sc = scoped
    ("Sig " ++ show sc)
    show
    (choice [ ("Object", return $ objS sc)
            , ("Morphism", do
                    let s = objS sc
                    x <- scoped "Source" show $ socEntityWithSig s
                    y <- scoped "Target" show $ socEntityWithSig s
                    return $ morS x y)
            , ("Proof", do
                    let s = objS sc
                    x <- scoped "Source" show $ socEntityWithSig s
                    y <- scoped "Target" show $ socEntityWithSig s
                    let t = morS x y
                    l <- scoped "Lhs"    show $ socEntityWithSig t
                    r <- scoped "Rhs"    show $ socEntityWithSig t
                    return $ prfS l r)
            , ("Lambda", do
                    s <- scoped "Argument" show $ socSig sc
                    b <- scoped "Body"     show $ socSig $ cons s
                    return $ lamS b)
            , ("Sigma", do
                    s <- scoped "First"  show $ socSig sc
                    t <- scoped "Second" show $ socSig $ cons s
                    return $ sgmS t)
            ])

socEntity :: Scope -> Socrates Entity
socEntity sc = scoped
    ("Entity " ++ show sc)
    show
    (socSig sc >>= socEntityWithSig)

socEntityWithSig :: Sig -> Socrates Entity
socEntityWithSig s = scoped
    ("Entity :: " ++ show s ++ " " ++ show (scope s))
    show
    (choice vars)

  where

    vars = map (show &&& return) $ filter (\v -> sig v == s) $ varsInScope (scope s)

varsInScope :: Scope -> [Entity]
varsInScope sc = reverse $ f sc where

    f sc' = case headTail sc' of
                   Nothing       -> []
                   Just (s, sc'') -> var s : map (lft s) (f sc'')
