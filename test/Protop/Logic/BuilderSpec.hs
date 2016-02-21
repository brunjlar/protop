module Protop.Logic.BuilderSpec (spec) where

import Protop.Logic.Builder
import Protop.Logic.Simple
import Test.Hspec

spec :: Spec
spec = do
    objBSpec
    addVarBSpec
    getVarBSpec
    lamSBSpec
    lftBSpec

objBSpec :: Spec
objBSpec = describe "objB" $

    it "should create a simple object signature" $ do
        let s = runBuilder objB
        show s   `shouldBe` "Ob"

addVarBSpec :: Spec
addVarBSpec = describe "addVarB" $ do

    it "should create a simple object variable" $ do
        let v = runBuilder $ do
                s <- objB
                addVarB "x" s
        showE v `shouldBe` "%1 :: Ob"

    it "should fail when called with a signature not in scope" $ do
        let mv = do
                sx <- objB
                let x = varE sx
                    s = morSIG x x
                addVarB "f" s
        putStrLn (showE $ runBuilder mv) `shouldThrow` anyException

getVarBSpec :: Spec
getVarBSpec = describe "getVarB" $ do

    it "should find an existing variable" $ do
        let v = runBuilder $ do
                s <- objB
                _ <- addVarB "x" s
                getVarB "x"
        showE v `shouldBe` "%1 :: Ob"

    it "should fail for a non-existing variable" $
        putStrLn (showE $ runBuilder $ getVarB "x") `shouldThrow` anyException

    it "should find a variable from an earlier scope" $ do
        let (x', y') = runBuilder $ do
                _ <- objB >>= addVarB "x"
                _ <- objB >>= addVarB "y"
                x <- getVarB "x"
                y <- getVarB "y"
                return (x, y)
        show x' `shouldBe` "%1"
        show y' `shouldBe` "%2"
        scopeE x' `shouldBe` scopeE y'

lamSBSpec :: Spec
lamSBSpec = describe "lamSB" $

    it "should create a lambda signature" $ do
        let s = runBuilder $ do
                x <- objB >>= addVarB "x"
                lamSB $ morSIG x x
        show s `shouldBe` "(\\(%1 :: Ob) -> (%1 -> %1))"

lftBSpec :: Spec
lftBSpec = describe "lftB" $

    it "should lift an entity" $ do
        let e = runBuilder $ do
                x  <- objB >>= addVarB "x"
                is <- lamSB $ morSIG x x
                _  <- addVarB "id" is
                y  <- objB >>= addVarB "y"
                i  <- getVarB "id"
                let iy = appE i y
                _  <- objB >>= addVarB "z"
                lftB iy
        showE e `shouldBe` "(%1 %2) :: (%2 -> %2)"
