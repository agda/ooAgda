module examplesPaperJFP.ConsoleInterface where

open import examplesPaperJFP.NativeIOSafe
open import examplesPaperJFP.BasicIO hiding (main)

module _ where
  data ConsoleCommand : Set where
    getLine   :  ConsoleCommand
    putStrLn  :  String → ConsoleCommand

  ConsoleResponse : ConsoleCommand → Set
  ConsoleResponse  getLine      =  Maybe String
  ConsoleResponse (putStrLn s)  =  Unit

  ConsoleInterface : IOInterface
  Command   ConsoleInterface  =  ConsoleCommand
  Response  ConsoleInterface  =  ConsoleResponse
