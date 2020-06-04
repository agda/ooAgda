module UnSized.Console where

open import UnSizedIO.Base  hiding (main)
open import UnSizedIO.Console  hiding (main)

open import NativeIO

{-# TERMINATING #-}
myProgram  :  IOConsole Unit
force myProgram =  exec' getLine          λ line  →
                   delay (exec' (putStrLn line)  λ _     →
                   delay (exec' (putStrLn line)  λ _     →
                   myProgram
                   ))


main  :  NativeIO Unit
main  =  translateIOConsole myProgram
