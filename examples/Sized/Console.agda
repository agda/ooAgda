module Sized.Console where

open import SizedIO.Base
open import SizedIO.Console hiding (main)

open import NativeIO

{-# TERMINATING #-}
myProgram  :  ∀{i} → IOConsole i Unit
myProgram  =  do  getLine          λ line →
              do  (putStrLn line)  λ _ →
              do  (putStrLn line)  λ _ →
              myProgram


main  :  NativeIO Unit
main  =  translateIOConsole myProgram
