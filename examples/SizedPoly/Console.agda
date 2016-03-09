module SizedPoly.Console where

open import SizedPolyIO.Base
open import SizedPolyIO.Console hiding (main)

open import NativePolyIO

open import Level using () renaming (zero to lzero)


{-# TERMINATING #-}
myProgram  :  ∀{i} → IOConsole i (Unit {lzero})
myProgram  =  do  getLine          λ line →
              do  (putStrLn line)  λ _ →
              do  (putStrLn line)  λ _ →
              myProgram


main  :  NativeIO Unit
main  =  translateIOConsole myProgram
