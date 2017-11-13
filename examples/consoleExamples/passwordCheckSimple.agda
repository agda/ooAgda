module consoleExamples.passwordCheckSimple where

open import ConsoleLib
open import Data.Bool.Base
open import Data.Bool
open import Data.String renaming (_==_ to _==str_)
open import SizedIO.Base

main : ConsoleProg
main = run (GetLine >>= λ s →
            if  s ==str "passwd"
            then  WriteString "Success"
            else  WriteString "Error")
