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
        scopeS s  `shouldBe` (cons (SIG sg) $ cons (SIG sf) $ cons (SIG sy) $ cons (SIG sx) empty)
        kindRep s `shouldBe` typeRep (Proxy :: Proxy 'PRF)


