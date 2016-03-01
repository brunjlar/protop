{-# LANGUAGE DataKinds #-}

module Protop.Logic.TypesSpec (spec) where

import Protop.Core
import Protop.Logic.Types
import Test.Hspec

spec :: Spec
spec = do
    objSSpec
    morSSpec
    prfSSpec
    lamSSpec
    sgmSSpec
    varSpec
    lamSpec
    appSpec
    sgmSpec
    compileSpec

objSSpec :: Spec
objSSpec = describe "objS" $

    it "should create an object signature in an empty context" $ do
        let s = objS Empty
        show s   `shouldBe` "Ob"
        scope s  `shouldBe` Empty

morSSpec :: Spec
morSSpec = describe "morS" $

    it "should create a simple morphism signature" $ do
        let o = objS Empty
            v = var o
            s = morS v v
        show s   `shouldBe` "(%1 -> %1)"
        scope s  `shouldBe` Cons o

prfSSpec :: Spec
prfSSpec = describe "prfS" $

    it "should create a simple proof signature" $ do
        let sx = objS Empty
            x  = var sx
            sy = objS (scope x)
            y  = var sy
            sf = morS (lft sy x) y
            f  = var sf
            sg = morS (lft sf (lft sy x)) (lft sf y)
            g  = var sg
            s  = prfS (lft sg f) g

        show s   `shouldBe` "(%3 == %4)"
        scope s  `shouldBe` Cons sg

lamSSpec :: Spec
lamSSpec = describe "lamS" $

    it "should create a simple lambda signature" $ do
        let s = prodSig

        show s  `shouldBe` "(\\(%1 :: Ob) -> (\\(%2 :: Ob) -> Ob))"
        scope s `shouldBe` Empty

sgmSSpec :: Spec
sgmSSpec = describe "sgmS" $

    it "should create a simple sigma signature" $ do
        let s = sgmSig
        show s  `shouldBe` "(Ex (%2 :: Ob) (%2 -> %1))"
        scope s `shouldBe` (Cons $ objS Empty)

varSpec :: Spec
varSpec = describe "var" $

    it "should create a variable with lambda signature" $ do
        let sp = prodSig
            p  = var sp
        show' p `shouldBe` "%1 :: (\\(%2 :: Ob) -> (\\(%3 :: Ob) -> Ob))"

lamSpec :: Spec
lamSpec = describe "lam" $ do

    it "should create a lambda" $ do
        let l' = xxEntity
        show l'       `shouldBe` "(\\(%1 :: (\\(%1 :: Ob) -> (\\(%2 :: Ob) -> Ob))) -> " ++
                                 "(\\(%2 :: Ob) -> ((%1 %2) %2)))"
        show (sig l') `shouldBe` "(\\(%1 :: (\\(%1 :: Ob) -> (\\(%2 :: Ob) -> Ob))) -> " ++
                                 "(\\(%2 :: Ob) -> Ob))"
        scope l'      `shouldBe` Empty

    it "should perform eta reduction" $ do
        let l  = var idSig
            sx = objS (scope l)
            x  = var sx
            l' = lft sx l
            lx = app l' x
            m  = lam lx
        show m `shouldBe` "%1"
        show (sig m) `shouldBe` "(\\(%2 :: Ob) -> (%2 -> %2))"

appSpec :: Spec
appSpec = describe "app" $ do

    it "should create an application using beta reduction" $ do
        let p   = var prodSig
            l   = lft prodSig xxEntity
            lp  = app l p
            sx  = objS $ scope lp
            x   = var sx
            lp' = lft sx lp
            lpx = app lp' x
        show lpx       `shouldBe` "((%1 %2) %2)"
        show (sig lpx) `shouldBe` "Ob"
        scope lpx      `shouldBe` scope x

    it "should create an application resulting in a morphism" $ do
        let sx = objS Empty
            x  = var sx
            sl = lft sx idSig
            l  = var sl
            x' = lft sl x
            lx = app l x'
        show lx       `shouldBe` "(%2 %1)"
        show (sig lx) `shouldBe` "(%1 -> %1)"

    it "should create an application resulting in a complicated morphism" $ do

        let sx = objS Empty
            x  = var sx
            sl = lft sx idSig
            l  = var sl
            sp = lft sl $ lft sx prodSig
            p  = var sp
            l' = lft sp l
            x' = lft sp $ lft sl x
            px = p `app` x'
            pxx = px `app` x'
            f  = l' `app` pxx
        show f       `shouldBe` "(%2 ((%3 %1) %1))"
        show (sig f) `shouldBe` "(((%3 %1) %1) -> ((%3 %1) %1))"

    it "should use beta reduction" $ do

        let p  = var prodSig
            q  = lft prodSig xxEntity
            l  = q `app` p
        show l `shouldBe` "(\\(%2 :: Ob) -> ((%1 %2) %2))"

sgmSpec :: Spec
sgmSpec = describe "sgm" $

    it "should create a simple sigma entity" $ do
        let i  = var idSig
            sx = lft idSig $ objS Empty
            x  = var sx
            s  = scLft (scope i) sgmSig
            i' = lft sx i
            f  = app i' x
            ex = sgm s x f
        show ex  `shouldBe` "<%2, (%1 %2)>"
        scope ex `shouldBe` Cons sx

compileSpec :: Spec
compileSpec = describe "compile" $ do

    it "should compile a simple object" $ do
        let sn = objS Empty
            n  = var sn
            sc = ConsM (Object N) EmptyM
            c  = compile n sc
        c `shouldBe` Object N

    it "should compile a lambda" $ do
        let p  = var prodSig
            sx = objS (scope p)
            x  = var sx
            p' = lft sx p
            e  = lam $ (p' `app` x) `app` x
            c  = compile e $ ConsM prodObject EmptyM
        c (Object N) `shouldBe` (Object $ N :* N)

prodSig :: Sig ('LAM 'OBJ ('LAM 'OBJ 'OBJ)) '[]
prodSig = let sx = objS Empty
              x  = var sx
              sy = objS (scope x)
              y  = var sy
              sp = objS (scope y)
              l1 = lamS sp
              l2 = lamS l1
          in  l2

xxEntity :: Entity ('LAM ('LAM 'OBJ ('LAM 'OBJ 'OBJ))
                         ('LAM 'OBJ 'OBJ))
                   '[]
xxEntity = let sp  = prodSig
               p   = var sp
               sx  = objS (scope p)
               x   = var sx
               p'  = lft sx p
               px  = p' `app` x
               pxx = px `app` x
               l   = lam pxx
               l'  = lam l
           in  l'

idSig :: Sig ('LAM 'OBJ 'MOR) '[]
idSig = let sx = objS Empty
            x  = var sx
            ms = morS x x
        in  lamS ms

prodObject :: Object -> Object -> Object
prodObject (Object x) (Object y) = Object (x :* y)

sgmSig :: Sig ('SGM 'OBJ 'MOR) '[ 'OBJ ]
sgmSig = let sx = objS Empty
             x  = var sx
             sy = objS (scope x)
             y  = var sy
             x' = lft sy x
             sf = morS y x'
         in  sgmS sf
