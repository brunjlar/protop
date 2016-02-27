module Protop.Logic.NewBuilderSpec (spec) where

import Protop.Logic.NewBuilder
import Test.Hspec

spec :: Spec
spec = do
    objBSpec

objBSpec :: Spec
objBSpec = describe "objB" $

    it "should create a simple object signature" $ do
        -- let s = runBuilder objB
        -- show s   `shouldBe` "Ob"
        True `shouldBe` False
