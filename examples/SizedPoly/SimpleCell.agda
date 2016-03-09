module SizedPoly.SimpleCell where

open import Data.Product
open import Data.String.Base

open import Size
open import Level using (_⊔_) renaming (suc to lsuc; zero to lzero)

open import SizedPolyIO.Object
open import SizedPolyIO.IOObject
open import SizedPolyIO.ConsoleObject

open import SizedPolyIO.Base
open import SizedPolyIO.Console hiding (main)

open import NativePolyIO

data CellMethod A : Set where
    get : CellMethod A
    put : A → CellMethod A

CellResponse : ∀{A} → CellMethod A → Set
CellResponse {A} get = A
CellResponse (put _) = Unit

-- cellI is the interface of the object of a simple cell
cellI : (A : Set) → Interface lzero lzero
Method  (cellI A)    =  CellMethod A
Result  (cellI A) m  =  CellResponse m

-- cellC is the type of consoleObjects with interface (cellI String)
CellC : (i : Size) → Set
CellC i = ConsoleObject i (cellI String)

-- cellP is constructor for the consoleObject for interface (cellI String)
cellP : ∀{i} (s : String) → CellC i
force (method (cellP s) get) =
  do' (putStrLn ("getting (" ++ s ++ ")")) λ _ →
  return (s , cellP s)
force (method (cellP s) (put x)) =
  do' (putStrLn ("putting (" ++ x ++ ")")) λ _ →
  return (_ , (cellP x))


-- Program is another program
program : String → IOConsole ∞ Unit
program arg =
  let c₀ = cellP "Start" in
  method c₀ get       >>= λ{ (s , c₁) →
  do1 (putStrLn s)         >>
  method c₁ (put arg) >>= λ{ (_ , c₂) →
  method c₂ get       >>= λ{ (s' , c₃) →
  do1 (putStrLn s')        }}}

main : NativeIO Unit
main = translateIOConsole (program "hello")
