module examplesPaperJFP.IOExampleConsole where

open import examplesPaperJFP.BasicIO hiding (main)
open import examplesPaperJFP.Console hiding (main)
open import examplesPaperJFP.NativeIOSafe
open import examplesPaperJFP.CatTerm

main : NativeIO Unit
main = translateIOConsole cat
