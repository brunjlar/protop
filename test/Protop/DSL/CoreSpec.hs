module Protop.DSL.CoreSpec (spec) where

import Protop.DSL

import Prelude    hiding ((.))
import Test.Hspec

spec :: Spec
spec = do
    sourceSpec
    targetSpec
    prfSpec
    compSpec

sourceSpec :: Spec
sourceSpec = describe "source" $

    it "should return the source of a morphism" $ do
        let x = Var "x" Obj
            y = Var "y" Obj
            f = Var "f" (Mor x y)
        source f `shouldBe` x

targetSpec :: Spec
targetSpec = describe "target" $

    it "should return the target of a morphism" $ do
        let x = Var "x" Obj
            y = Var "y" Obj
            f = Var "f" (Mor x y)
        target f `shouldBe` y 

prfSpec :: Spec
prfSpec = describe "prf" $ do

    let x = Var "x" Obj
        y = Var "y" Obj
        f = Var "f" (Mor x y)
        g = Var "g" (Mor x y)

    it "should construct a proof signature from two morphisms with equal signature" $ do
        show <$> prf f g `shouldBe` Right "(f == g)"

    it "should fail, given morphisms with different sources" $
        prf f (Id y) `shouldBe` Left (ExpectedEqualObjects x y)

    it "should fail, given morphisms with different targets" $
        prf f (Id x) `shouldBe` Left (ExpectedEqualObjects y x)

compSpec :: Spec
compSpec = describe "(.)" $ do

    it "should compose composable morphisms" $ do
        let x = Var "x" Obj
            y = Var "y" Obj
            z = Var "z" Obj
            f = Var "f" (Mor y z)
            g = Var "g" (Mor x y)
        show <$> (f . g) `shouldBe` Right "(f . g)"

    it "should fail, given incomposable morphisms" $ do
        let x = Var "x" Obj
            y = Var "y" Obj
            f = Var "f" (Mor x y)
        (f . f) `shouldBe` Left (ExpectedEqualObjects x y)
        

force :: Either DSLException a -> a
force (Right a) = a
force (Left e)  = error (show e)
