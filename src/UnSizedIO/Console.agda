module UnSizedIO.Console where

open import NativeIO
open import UnSizedIO.Base hiding (main)

data ConsoleCommand : Set where
  putStrLn : String → ConsoleCommand
  getLine  : ConsoleCommand

ConsoleResponse : ConsoleCommand → Set
ConsoleResponse (putStrLn s) = Unit
ConsoleResponse  getLine     = String

ConsoleInterface : IOInterface
Command  ConsoleInterface = ConsoleCommand
Response ConsoleInterface = ConsoleResponse

IOConsole : Set → Set
IOConsole = IO ConsoleInterface

IOConsole+ : Set → Set
IOConsole+ = IO+ ConsoleInterface

translateIOConsoleLocal : (c : ConsoleCommand) → NativeIO (ConsoleResponse c)
translateIOConsoleLocal (putStrLn s) = nativePutStrLn s
translateIOConsoleLocal getLine      = nativeGetLine

translateIOConsole : {A : Set} → IOConsole A → NativeIO A
translateIOConsole = translateIO translateIOConsoleLocal

main : NativeIO Unit
main = nativePutStrLn "Console"
