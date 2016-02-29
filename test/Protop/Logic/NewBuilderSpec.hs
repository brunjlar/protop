module Protop.Logic.NewBuilderSpec (spec) where

import Prelude hiding (return, (>>=), (>>))
import Protop.Logic.NewBuilder
import Test.Hspec

spec :: Spec
spec = do
    morMSpec

morMSpec :: Spec
morMSpec = describe "morM" $ do

    it "should find properly lift objects" $ do
        let s = objM >>= varM >>= \x ->
                objM >>= varM >>= \y ->
                morM x y >>=      \f ->
                popM >> popM >>
                return f
        show (evalM s) `shouldBe` "(%1 -> %2)"

    it "should throw an exception when lifting is unsound" $ do

        let s = objM     >>= varM >>= \x ->
                objM     >>= varM >>= \y ->
                morM x y >>= varM >>= \f ->
                popM >>
                lftM f            >>= \t ->
                popM >> popM >>
                return t
        print (evalM s) `shouldThrow` anyErrorCall
