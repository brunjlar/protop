module Protop.Logic.BuilderSpec (spec) where

import Control.Monad ((>=>))
import Protop.Logic
import Test.Hspec

spec :: Spec
spec = do
    morMSpec
    prfMSpec
    lamSMSpec
    sgmSMSpec
    lamMSpec
    appMSpec
    sgmMSpec

morMSpec :: Spec
morMSpec = describe "morM" $ do

    it "should properly lift objects" $ do
        let s = objM >>= varM >>= \x ->
                objM >>= varM >>= \y ->
                morM x y >>=      \f ->
                popM >> popM >>
                return f
            e = evalM s
        show e `shouldBe` "(%1 -> %2)"
        kind e `shouldBe` MOR

    it "should throw an exception when lifting is unsound" $ do

        let s = objM    >>= varM  >>= \x ->
                objM    >>= varM  >>=
                (morM x >=> varM) >>= \f ->
                popM >>
                lftM f            >>= \t ->
                popM >> popM >>
                return t
        print (evalM s) `shouldThrow` anyErrorCall

prfMSpec :: Spec
prfMSpec = describe "prfM" $

    it "should create a simple proof signature" $ do
        let s = objM     >>= varM >>= \x ->
                objM     >>= varM >>= \y ->
                morM x y >>= varM >>= \f ->
                morM x y >>= varM >>=
                (prfM f  >=>          \p ->
                popM >> popM >> popM >> popM >>
                return p)
            e = evalM s
        show e `shouldBe` "(%3 == %4)"
        kind e `shouldBe` PRF

lamSMSpec :: Spec
lamSMSpec = describe "lamSM" $

    it "should create a simple lambda signature" $ do
        let s = objM     >>= varM  >>= \x ->
                morM x x >>= lamSM
            e = evalM s
        show e `shouldBe` "(\\(%1 :: Ob) -> (%1 -> %1))"
        kind e `shouldBe` (LAM OBJ MOR)

sgmSMSpec :: Spec
sgmSMSpec = describe "sgmSM" $

    it "should create a simple sigma signature" $ do
        let s = objM     >>= varM >>= \t ->
                objM     >>= varM >>= \x ->
                morM x t >>= lamSM >>= sgmSM
            e = evalM s
        show e `shouldBe` "(Ex (%1 :: Ob) (\\(%2 :: Ob) -> (%2 -> %1)))"
        kind e `shouldBe` (SGM OBJ (LAM OBJ MOR))

lamMSpec :: Spec
lamMSpec = describe "lamM" $

    it "should create a simple lambda entity" $ do
        let s = objM >>= varM >>= lamM
            e = evalM s
        show e `shouldBe` "(\\(%1 :: Ob) -> %1)"
        kind e `shouldBe` (LAM OBJ OBJ)

appMSpec :: Spec
appMSpec = describe "appM" $

    it "should create a simple application" $ do
        let s = objM >>= varM >>= \_ ->
                objM >>= varM >>= \_ ->
                objM >>= lamSM >>= lamSM >>= varM >>= \p ->
                objM >>= varM >>= \x ->
                appM p x >>= \px ->
                appM px x >>= \pxx ->
                popM >> popM >>
                return pxx
            e = evalM s
        show e `shouldBe` "((%1 %2) %2)"
        kind e `shouldBe` OBJ

sgmMSpec :: Spec
sgmMSpec = describe "sgmM" $

    it "should create a simple sigma pair" $ do
        let s = objM     >>= varM  >>= \x ->
                morM x x >>= varM  >>= \f ->
                objM     >>= varM  >>= \y ->
                morM y x >>= sgmSM >>= \t ->
                sgmM t x f         >>= \g ->
                popM >> popM >>
                return g
            e = evalM s
        show' e `shouldBe` "<%1, %2> :: (Ex (%3 :: Ob) (%3 -> %1))"
        kind e `shouldBe` (SGM OBJ MOR)

