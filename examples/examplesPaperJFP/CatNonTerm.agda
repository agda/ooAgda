module examplesPaperJFP.CatNonTerm where

open import examplesPaperJFP.BasicIO hiding (main)
open import examplesPaperJFP.Console hiding (main)
open import examplesPaperJFP.NativeIOSafe
module _ where
  {-# NON_TERMINATING #-}
  cat  :  IO ConsoleInterface Unit
  cat  =  do' getLine                         λ{ nothing    → return unit ;
                                                (just line) →
           do' (putStrLn line)                 λ _ →
           cat                                }
