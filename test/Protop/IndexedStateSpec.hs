module Protop.IndexedStateSpec (spec) where

import Control.Arrow       ((&&&))
import Prelude hiding      (return, (>>=), (>>), fail)
import Protop.IndexedState
import Test.Hspec

spec :: Spec
spec = do
    runIStateSpec
    evalIStateSpec
    execIStateSpec
    fmapSpec
    returnSpec
    bindSpec
    thenSpec
    failSpec
    joinSpec
    getSpec
    putSpec
    modifySpec

runIStateSpec :: Spec
runIStateSpec = describe "runIState" $

    it "should run a stateful computation" $ do
        runIState s 42 `shouldBe` (True, "42")
        runIState s 17 `shouldBe` (False, "17")

evalIStateSpec :: Spec
evalIStateSpec = describe "evalIState" $

    it "should evaluate a stateful computation" $ do
        evalIState s 42 `shouldBe` True
        evalIState s 17 `shouldBe` False

execIStateSpec :: Spec
execIStateSpec = describe "execIState" $

    it "should execute a stateful computation" $ do
        execIState s 42 `shouldBe` "42"
        execIState s 17 `shouldBe` "17"

fmapSpec :: Spec
fmapSpec = describe "fmap" $

    it "should lift a function to stateful computations" $ do
        runIState (not <$> s) 42 `shouldBe` (False, "42")
        runIState (not <$> s) 17 `shouldBe` (True, "17")

returnSpec :: Spec
returnSpec = describe "return" $

    it "should turn a pure value into a stateful computation" $ do
        let n = 42 :: Int
        runIState (return n) "Lars" `shouldBe` (n, "Lars")

bindSpec :: Spec
bindSpec = describe "bind" $

    it "should chain two stateful computations" $ do
        let t = s' >>= \x ->
                s  >>= \b ->
                return $ x ++ show b
        runIState t "Lars" `shouldBe` ("LarsTrue", "4")
        runIState t "Haskell" `shouldBe` ("HaskellFalse", "7")

thenSpec :: Spec
thenSpec = describe "then" $

    it "should chain two stateful computations, ignoring the first result" $ do
        let t = s' >>
                s  >>= \b ->
                return b
        runIState t "Lars" `shouldBe` (True, "4")
        runIState t "Haskell" `shouldBe` (False, "7")

failSpec :: Spec
failSpec = describe "fail" $

    it "should fail a stateful computation" $ do
        let t = s >> fail "Test" :: IState Int (Maybe Bool) Char
        print (runIState t 42) `shouldThrow` anyErrorCall

joinSpec :: Spec
joinSpec = describe "join" $

    it "should join a nested stateful computation" $ do
        let m = IState $ \x -> (IState $ show &&& even, length x)
        runIState (join m) "Lars" `shouldBe` ("4", True)
        runIState (join m) "Haskell" `shouldBe` ("7", False)

getSpec :: Spec
getSpec = describe "get" $

    it "should get the state of a stateful computation" $ do
        evalIState (s >> get) 42 `shouldBe` "42"
        evalIState (s' >> get) "Lars" `shouldBe` 4

putSpec :: Spec
putSpec = describe "put" $

    it "should set the state of a stateful computation" $ do
        execIState (s >> put 'x') 42 `shouldBe` 'x'
        execIState (s' >> put "Haskell") "Lars" `shouldBe` "Haskell"

modifySpec :: Spec
modifySpec = describe "modify" $

    it "should modify the state of a stateful computation" $ do
        execIState (s >> modify length) 42 `shouldBe` 2
        execIState (s' >> modify succ) "Lars" `shouldBe` 5

s :: IState Int String Bool
s = IState $ even &&& show

s' :: IState String Int String
s' = IState $ id &&& length
