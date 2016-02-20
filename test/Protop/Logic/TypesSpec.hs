{-# LANGUAGE DataKinds #-}

module Protop.Logic.TypesSpec (spec) where

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
        scope s  `shouldBe` (Cons sg)

lamSSpec :: Spec
lamSSpec = describe "lamS" $

    it "should create a simple lambda signature" $ do
        let s = prodSig

        show s    `shouldBe` "(\\(%1 :: Ob) -> (\\(%2 :: Ob) -> Ob))"
        scope s  `shouldBe` Empty

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
        scope l'      `shouldBe` Empty

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
        putStrLn $ show lpx
        show lpx       `shouldBe` "(((\\(%3 :: (\\(%3 :: Ob) -> (\\(%4 :: Ob) -> Ob)))" ++
                                  " -> (\\(%4 :: Ob) -> ((%3 %4) %4))) %1) %2)"
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
            sp = lft sl $ lft sx $ prodSig
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
        show l `shouldBe` ""

prodSig :: Sig '[] ('LAM 'OBJ ('LAM 'OBJ 'OBJ))
prodSig = let sx = objS Empty
              x  = var sx
              sy = objS (scope x)
              y  = var sy
              sp = objS (scope y)
              l1 = lamS sp
              l2 = lamS l1
          in  l2

xxEntity :: Entity '[] ('LAM ('LAM 'OBJ ('LAM 'OBJ 'OBJ))
                             ('LAM 'OBJ 'OBJ))
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

idSig :: Sig '[] ('LAM 'OBJ 'MOR)
idSig = let sx = objS Empty
            x  = var sx
            ms = morS x x
        in  lamS ms
