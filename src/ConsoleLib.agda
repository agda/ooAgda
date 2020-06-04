module ConsoleLib where

open import NativeIO public
open import SizedIO.Console public  hiding (main) renaming (translateIOConsole to run)
open import Size
open import SizedIO.Base
open import Data.List

WriteString : (s : String) → IOConsole ∞ Unit
WriteString s = Exec (putStrLn s)

GetLine : IOConsole ∞ String
GetLine = Exec getLine

ConsoleProg : Set
ConsoleProg = NativeIO Unit
