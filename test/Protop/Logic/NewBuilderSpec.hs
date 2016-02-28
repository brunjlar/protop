module Protop.Logic.NewBuilderSpec (spec) where

import Prelude hiding (return, (>>=), (>>))
import Protop.Logic.NewBuilder
import Protop.Logic.Types
import Test.Hspec

spec :: Spec
spec = do
    varMSpec

varMSpec :: Spec
varMSpec = describe "varM" $ do

    it "should find previously defined variables" $ do
        let s = objM >>= pushM "x" >>
                objM >>= pushM "y" >>
                varM "x" >>= \x ->
                varM "y" >>= \y ->
                popM >>
                popM >>
                return (morS x y)
        show (evalM s) `shouldBe` "(%1 -> %2)"

    it "should throw an exception when used with the wrong kind" $ do
        let s = objM >>= pushM "x" >>
                objM >>= pushM "y" >>
                varM "x" >>= \x ->
                pushM "f" (morS x x) >>
                varM "f" >>= \f ->
                varM "y" >>= \y ->
                popM >>
                popM >>
                popM >>
                return (morS f y)
        print (evalM s) `shouldThrow` anyErrorCall
