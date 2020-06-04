module examplesPaperJFP.CatNonTerm where

open import examplesPaperJFP.BasicIO hiding (main)
open import examplesPaperJFP.Console hiding (main)
open import examplesPaperJFP.NativeIOSafe
module _ where
  {-# NON_TERMINATING #-}
  cat  :  IO ConsoleInterface Unit
  cat  =  exec getLine                         λ{ nothing    → return unit ;
                                                (just line) →
           exec (putStrLn line)                 λ _ →
           cat                                }
