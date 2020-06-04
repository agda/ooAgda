module helloWorld where

open import ConsoleLib

main : ConsoleProg
main = run (WriteString "Hello World")
