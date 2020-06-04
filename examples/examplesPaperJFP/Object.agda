module examplesPaperJFP.Object where

open import Data.Product
open import Data.String.Base

open import examplesPaperJFP.NativeIOSafe
open import examplesPaperJFP.BasicIO hiding (main)
open import examplesPaperJFP.Console hiding (main)

record Interface  :  Set₁ where
  field  Method   :  Set
         Result   :  (m : Method) → Set

open Interface public

record Object (I : Interface) : Set where
  coinductive
  field objectMethod : (m : Method I) → Result I m × Object I


open Object public

record IOObject (Iᵢₒ : IOInterface) (I : Interface) : Set where
  coinductive
  field method : (m : Method I) → IO Iᵢₒ (Result I m × IOObject Iᵢₒ I)

open IOObject public



data CellMethod A : Set where
    get  :  CellMethod A
    put  :  A → CellMethod A

CellResult             :  ∀{A} → CellMethod A → Set
CellResult   {A} get   =  A
CellResult   (put _)   =  Unit

cellJ                  :  (A : Set) → Interface
Method    (cellJ A)    =  CellMethod A
Result    (cellJ A) m  =  CellResult m

CellC : Set
CellC = IOObject ConsoleInterface (cellJ String)

simpleCell : (s : String) → CellC
force (method (simpleCell s) get) =
  exec′ (putStrLn ("getting (" ++ s ++ ")")) λ _ →
  delay (return′ (s , simpleCell s))
force (method (simpleCell s) (put x)) =
  exec′ (putStrLn ("putting (" ++ x ++ ")")) λ _ →
  delay (return′ (unit , simpleCell x))

{-# TERMINATING #-}

program : IOConsole Unit
force program =
  let c₁ = simpleCell "Start" in
  exec′ getLine          λ{ nothing → return unit; (just s) →
  method c₁ (put s)    >>= λ{ (_ , c₂) →
  method c₂ get        >>= λ{ (s′ , _ ) →
  exec (putStrLn s′)     λ _ →
  program }}}

main : NativeIO Unit
main = translateIOConsole program
