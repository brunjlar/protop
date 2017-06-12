module Protop.DSL.CoreSpec (spec) where

import Control.Monad.Except (MonadError (..))
import Test.Hspec

import Protop.DSL

spec :: Spec
spec = do
    sourceSpec
    targetSpec
    lhsSpec
    rhsSpec
    prfSpec
    appSpec

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

lhsSpec :: Spec
lhsSpec = describe "lhs" $

    it "should return the left hand side of a proof" $ do
        let x = Var "x" Obj
            y = Var "y" Obj
            f = Var "f" (Mor x y)
            g = Var "g" (Mor x y)
            p = Var "p" $ force $ prf f g
        lhs p `shouldBe` f 

rhsSpec :: Spec
rhsSpec = describe "rhs" $

    it "should return the right hand side of a proof" $ do
        let x = Var "x" Obj
            y = Var "y" Obj
            f = Var "f" (Mor x y)
            g = Var "g" (Mor x y)
            p = Var "p" $ force $ prf f g
        rhs p `shouldBe` g 

prfSpec :: Spec
prfSpec = describe "prf" $ do

    let x = Var "x" Obj
        y = Var "y" Obj
        f = Var "f" (Mor x y)
        g = Var "g" (Mor x y)
        h = Var "h" (Mor x x)
        i = Var "i" (Mor y y)

    it "should construct a proof signature from two morphisms with equal signature" $ do
        show <$> prf f g `shouldBe` Right "(f == g)"

    it "should fail, given morphisms with different sources" $
        prf f i `shouldBe` Left (DistinctSignatures (Mor x y) (Mor y y))

    it "should fail, given morphisms with different targets" $
        prf f h `shouldBe` Left (DistinctSignatures (Mor x y) (Mor x x))

appSpec :: Spec
appSpec = describe "app" $ do

    let x = Var "x" Obj
        y = Var "y" Obj
        e = Lambda "f" (Mor x y) (Var "f" (Mor x y))

    it "should apply a lambda to an argument with the right signature" $
        show <$> app e (Var "g" (Mor x y)) `shouldBe` Right "((\\f -> f) g)"
        
    it "should fail, gien an argument with the wrong signature" $
        app e (Var "g" (Mor x x)) `shouldBe` Left (DistinctSignatures (Mor x x) (Mor x y))

force :: (forall m. MonadError DSLException m => m a) -> a
force m = case m of
    Right x -> x
    Left e  -> error $ show e
