module Sized.SimpleCell where

open import Data.Product
open import Data.String.Base

open import SizedIO.Object
open import SizedIO.IOObject
open import SizedIO.ConsoleObject

open import SizedIO.Base
open import SizedIO.Console hiding (main)

open import NativeIO

open import Size

data CellMethod A : Set where
    get : CellMethod A
    put : A → CellMethod A

CellResult : ∀{A} → CellMethod A → Set
CellResult {A} get = A
CellResult (put _) = Unit

-- cellI is the interface of the object of a simple cell
cellI : (A : Set) → Interface
Method  (cellI A)    =  CellMethod A
Result  (cellI A) m  =  CellResult m

-- cellC is the type of consoleObjects with interface (cellI String)
CellC : (i : Size) → Set
CellC i = ConsoleObject i (cellI String)


-- cellO is a program for a simple cell which
-- when get is called writes "getting s" for the string s of the object
-- and when putting s writes "putting s" for the string

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
  do1 (putStrLn s')
  }}}

main : NativeIO Unit
main = translateIOConsole (program "hello")
