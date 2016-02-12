module Protop.Core.NaturalSpec (spec) where

import Protop.Core
import Test.Hspec

spec :: Spec
spec = do
    addSpec
    mulSpec

addSpec :: Spec
addSpec = describe "add" $

    it "should add natural numbers" $
        (add .$. (42, 8)) `shouldBe` 50

mulSpec :: Spec
mulSpec = describe "mul" $

    it "should multiply natural numbers" $
        (mul .$. (11, 12)) `shouldBe` 132
