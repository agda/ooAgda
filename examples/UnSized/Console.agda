module UnSized.Console where

open import UnSizedIO.Base  hiding (main)
open import UnSizedIO.Console  hiding (main)

open import NativeIO

{-# TERMINATING #-}
myProgram  :  IOConsole Unit
force myProgram =  do' getLine          λ line  →
                   delay (do' (putStrLn line)  λ _     →
                   delay (do' (putStrLn line)  λ _     →
                   myProgram
                   ))


main  :  NativeIO Unit
main  =  translateIOConsole myProgram
