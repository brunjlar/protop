module Protop.TVaultSpec (spec) where

import           Data.Proxy    (Proxy(..))
import qualified Protop.TVault as V
import           Test.Hspec

spec :: Spec
spec = lookupSpec

lookupSpec :: Spec
lookupSpec = describe "lookup" $ do

    it "should return Nothing for an empty vault" $
        V.lookup (Proxy :: Proxy Int) V.empty `shouldBe` Nothing

    it "should retrieve the value that has been stored" $
        V.lookup Proxy (V.insert "Lars" V.empty) `shouldBe` Just "Lars"

    it "should return Nothing if no value of the queried type has been stored" $
        V.lookup (Proxy :: Proxy String) (V.insert False V.empty) `shouldBe` Nothing

    it "should be possible to store and retrieve values with different types" $ do
        let v = V.insert "Lars" $ V.insert True V.empty
        V.lookup Proxy v `shouldBe` Just True
        V.lookup Proxy v `shouldBe` Just "Lars"
