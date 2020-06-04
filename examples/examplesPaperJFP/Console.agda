module examplesPaperJFP.Console where

open import  examplesPaperJFP.NativeIOSafe
open import  examplesPaperJFP.BasicIO hiding (main)
open import  examplesPaperJFP.ConsoleInterface public

IOConsole : Set → Set
IOConsole = IO ConsoleInterface

--IOConsole+ : Set → Set
--IOConsole+ = IO+ ConsoleInterface

translateIOConsoleLocal : (c : ConsoleCommand) → NativeIO (ConsoleResponse c)
translateIOConsoleLocal (putStrLn s)  =  nativePutStrLn s
translateIOConsoleLocal getLine       =  nativeGetLine

translateIOConsole : {A : Set} → IOConsole A → NativeIO A
translateIOConsole = translateIO translateIOConsoleLocal

main : NativeIO Unit
main = nativePutStrLn "Console"
