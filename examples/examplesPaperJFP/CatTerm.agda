module examplesPaperJFP.CatTerm where

open import examplesPaperJFP.BasicIO hiding (main)
open import examplesPaperJFP.Console hiding (main)
open import examplesPaperJFP.NativeIOSafe

cat : IO ConsoleInterface Unit
force cat =
  do'′ getLine          λ{ nothing → return unit ; (just line) → delay (
  do'′ (putStrLn line)  λ _     →
  cat                  )}
