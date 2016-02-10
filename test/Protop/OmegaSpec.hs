module Protop.OmegaSpec (spec) where

import Protop
import Test.Hspec

spec :: Spec
spec = omegaSpec

omegaSpec :: Spec
omegaSpec = describe "Omega" $

    it "must be possible to construct a simple morphism into a subobject" $
        let two = Succ :. Succ :. Zero
            m   = let t  = MonoTest1 two
                      t' = MonoTest2 two
                  in  TERMINAL t :> SYMM (TERMINAL t')
            te  = Terminal (N :* N)
            g   = two :. te
            sub = Sub two m
            q   = SYMM (ASS sub two te) :>
                  (SUB two m :|. te) :>
                  ASS True' (Terminal T) te :>
                  (True' :.| TERMINAL (Terminal T :. te))
            o   = Omega two m g q
        in (o .$ (2, 3)) `shouldBe` star
