{-# LANGUAGE DataKinds #-}

module Protop.Logic.TypesSpec (spec) where

import Data.Proxy    (Proxy(..))
import Data.Typeable (typeRep)
import Protop.Logic
import Test.Hspec

spec :: Spec
spec = do
    objSSpec
    morSSpec
    prfSSpec
    lamSSpec
    varSpec
    lamSpec
    appSpec

objSSpec :: Spec
objSSpec = describe "objS" $

    it "should create an object signature in an empty context" $ do
        let s = objS empty
        show s    `shouldBe` "Ob"
        scopeS s  `shouldBe` empty
        kindRep s `shouldBe` typeRep (Proxy :: Proxy 'OBJ)

morSSpec :: Spec
morSSpec = describe "morS" $

    it "should create a simple morphism signature" $ do
        let o = objS empty
            v = var o
            s = morS v v
        show s    `shouldBe` "(%1 -> %1)"
        scopeS s  `shouldBe` cons (SIG o)
        kindRep s `shouldBe` typeRep (Proxy :: Proxy 'MOR)

prfSSpec :: Spec
prfSSpec = describe "prfS" $

    it "should create a simple proof signature" $ do
        let sx = objS empty
            x  = var sx
            sy = objS (scope x)
            y  = var sy
            sf = morS (lft sy x) y
            f  = var sf
            sg = morS (lft sf (lft sy x)) (lft sf y)
            g  = var sg
            s  = prfS (lft sg f) g

        show s    `shouldBe` "(%3 == %4)"
        scopeS s  `shouldBe` (cons (SIG sg))
        kindRep s `shouldBe` typeRep (Proxy :: Proxy 'PRF)

lamSSpec :: Spec
lamSSpec = describe "lamS" $

    it "should create a simple lambda signature" $ do
        let s = prodSig

        show s    `shouldBe` "(\\(%1 :: Ob) -> (\\(%2 :: Ob) -> Ob))"
        scopeS s  `shouldBe` empty
        kindRep s `shouldBe` typeRep (Proxy :: Proxy ('LAM 'OBJ ('LAM 'OBJ 'OBJ)))

varSpec :: Spec
varSpec = describe "var" $ do

    it "should create a variable with lambda signature" $ do
        let sp = prodSig
            p  = var sp
        (show' p) `shouldBe` "%1 :: (\\(%2 :: Ob) -> (\\(%3 :: Ob) -> Ob))"

lamSpec :: Spec
lamSpec = describe "lam" $ do

    it "should create a lambda" $ do
        let l' = xxEntity
        show l'       `shouldBe` "(\\(%1 :: (\\(%1 :: Ob) -> (\\(%2 :: Ob) -> Ob))) -> " ++
                                 "(\\(%2 :: Ob) -> ((%1 %2) %2)))"
        show (sig l') `shouldBe` "(\\(%1 :: (\\(%1 :: Ob) -> (\\(%2 :: Ob) -> Ob))) -> " ++
                                 "(\\(%2 :: Ob) -> Ob))"
        scope l'      `shouldBe` empty
        kindRep l'    `shouldBe` typeRep (Proxy :: Proxy ('LAM ('LAM 'OBJ ('LAM 'OBJ 'OBJ))
                                                         ('LAM 'OBJ 'OBJ)))

appSpec :: Spec
appSpec = describe "app" $ do

    it "should create an application resulting in an object" $ do
        let p   = var prodSig
            l   = lft prodSig xxEntity
            lp  = app l p
            sx  = objS $ scope lp
            x   = var sx
            lp' = lft sx lp 
            lpx = app lp' x
        show lpx       `shouldBe` "(((\\(%1 :: (\\(%1 :: Ob) -> (\\(%2 :: Ob) -> Ob))) -> " ++
                                  "(\\(%2 :: Ob) -> ((%1 %2) %2))) %1) %2)"
        show (sig lpx) `shouldBe` "Ob"
        scope lpx      `shouldBe` scope x
        kindRep lpx    `shouldBe` typeRep (Proxy :: Proxy 'OBJ)

    it "should create an application resulting in a morphism" $ do
        let sx = objS empty
            x  = var sx
            sl = lftS sx idSig
            l  = var sl
            x' = lft sl x
            lx = app l x'
        show lx       `shouldBe` "(%2 %1)"
        show (sig lx) `shouldBe` "(%1 -> %1)"
        kindRep lx    `shouldBe` typeRep (Proxy :: Proxy 'MOR)

    it "should create an application resulting in a complicated morphism" $ do

        let sx = objS empty
            x  = var sx
            sl = lftS sx idSig
            l  = var sl
            sp = lftS sl $ lftS sx $ prodSig
            p  = var sp
            l' = lft sp l
            x' = lft sp $ lft sl x
            px = p `app` x'
            pxx = px `app` x'
            f  = l' `app` pxx
        show f       `shouldBe` "(%2 ((%3 %1) %1))"
        show (sig f) `shouldBe` "(((%3 %1) %1) -> ((%3 %1) %1))"
        kindRep f    `shouldBe` typeRep (Proxy :: Proxy 'MOR)

prodSig :: Sig ('LAM 'OBJ ('LAM 'OBJ 'OBJ))
prodSig = let sx = objS empty
              x  = var sx
              sy = objS (scope x)
              y  = var sy
              sp = objS (scope y)
              l1 = lamS (Proxy :: Proxy 'OBJ) sp
              l2 = lamS (Proxy :: Proxy 'OBJ) l1
          in  l2

xxEntity :: Entity ('LAM ('LAM 'OBJ ('LAM 'OBJ 'OBJ))
                         ('LAM 'OBJ 'OBJ))
xxEntity = let sp  = prodSig
               p   = var sp
               sx  = objS (scope p)
               x   = var sx
               p'  = lft sx p
               px  = p' `app` x
               pxx = px `app` x
               l   = lam (Proxy :: Proxy 'OBJ) pxx
               l'  = lam (Proxy :: Proxy ('LAM 'OBJ ('LAM 'OBJ 'OBJ))) l
           in  l'

idSig :: Sig ('LAM 'OBJ 'MOR)
idSig = let sx = objS empty
            x  = var sx
            ms = morS x x
        in  lamS (Proxy :: Proxy 'OBJ) ms
