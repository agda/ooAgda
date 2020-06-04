module UnSized.SimpleCell where

open import Data.Product
open import Data.String.Base

open import UnSizedIO.Object
open import UnSizedIO.IOObject
open import UnSizedIO.ConsoleObject

open import UnSizedIO.Base hiding (main)
open import UnSizedIO.Console hiding (main)

open import NativeIO

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
CellC : Set
CellC = ConsoleObject (cellI String)


-- cellO is a program for a simple cell which
-- when get is called writes "getting s" for the string s of the object
-- and when putting s writes "putting s" for the string

-- cellP is constructor for the consoleObject for interface (cellI String)
cellP : (s : String) → CellC
force (method (cellP s) get) =
  exec' (putStrLn ("getting (" ++ s ++ ")")) λ _ →
  delay (return' (s , cellP s))
force (method (cellP s) (put x)) =
  exec' (putStrLn ("putting (" ++ x ++ ")")) λ _ →
  delay (return' (_ , (cellP x)))

-- Program is another program

program : String → IOConsole Unit
program arg =
  let c₀ = cellP "Start" in
  method c₀ get       >>= λ{ (s , c₁) →
  exec1 (putStrLn s)         >>
  method c₁ (put arg) >>= λ{ (_ , c₂) →
  method c₂ get       >>= λ{ (s' , c₃) →
  exec1 (putStrLn s')        }}}

main : NativeIO Unit
main = translateIOConsole (program "hello")
