module SizedPoly.Console where

open import SizedPolyIO.Base
open import SizedPolyIO.Console hiding (main)

open import NativePolyIO

open import Level using () renaming (zero to lzero)


{-# TERMINATING #-}
myProgram  :  ∀{i} → IOConsole i (Unit {lzero})
myProgram  =  exec  getLine          λ line →
              exec  (putStrLn line)  λ _ →
              exec  (putStrLn line)  λ _ →
              myProgram


main  :  NativeIO Unit
main  =  translateIOConsole myProgram
