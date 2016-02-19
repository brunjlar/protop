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
    --lamSpec

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
        scopeS s  `shouldBe` cons (SIG o) empty
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
        scopeS s  `shouldBe` (cons (SIG sg) $ cons (SIG sf) $
                              cons (SIG sy) $ cons (SIG sx) empty)
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
        (show' p) `shouldBe` "%1 :: (\\(%1 :: Ob) -> (\\(%2 :: Ob) -> Ob))"

lamSpec :: Spec
lamSpec = describe "lam" $ do

    it "should create a simple lambda" $ do
        let sp = prodSig
            p  = var sp
            sx = objS (scope p)
            x  = var sx
            p' = lft sx p
            px = p' `app` x
            spx = sig px
            l  = px `app` x
        show' (p' `app` x) `shouldBe` "XXX"

prodSig :: Sig ('LAM 'OBJ ('LAM 'OBJ 'OBJ))
prodSig = let sx = objS empty
              x  = var sx
              sy = objS (scope x)
              y  = var sy
              sp = objS (scope y)
              l1 = lamS (Proxy :: Proxy 'OBJ) sp
              l2 = lamS (Proxy :: Proxy 'OBJ) l1
          in  l2

idSig :: Sig ('LAM 'OBJ 'MOR)
idSig = let sx = objS empty
            x  = var sx
            sm = morS x x
        in  lamS (Proxy :: Proxy 'OBJ) sm
