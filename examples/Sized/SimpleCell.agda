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

-- cellJ is the interface of the object of a simple cell
cellJ : (A : Set) → Interface
Method  (cellJ A)    =  CellMethod A
Result  (cellJ A) m  =  CellResult m

cell : {A : Set} → A → Object (cellJ A)
objectMethod (cell a) get = a , (cell a)
objectMethod (cell a) (put a') = _ , (cell a')

-- cellC is the type of consoleObjects with interface (cellJ String)
CellC : (i : Size) → Set
CellC i = ConsoleObject i (cellJ String)


-- cellO is a program for a simple cell which
-- when get is called writes "getting s" for the string s of the object
-- and when putting s writes "putting s" for the string

-- cellP is constructor for the consoleObject for interface (cellJ String)
cellP : ∀{i} (s : String) → CellC i
force (method (cellP s) get) =
  exec' (putStrLn ("getting (" ++ s ++ ")")) λ _ →
  return (s , cellP s)
force (method (cellP s) (put x)) =
  exec' (putStrLn ("putting (" ++ x ++ ")")) λ _ →
  return (_ , (cellP x))

-- Program is another program
program : String → IOConsole ∞ Unit
program arg =
  let c₀ = cellP "Start" in
  method c₀ get       >>= λ{ (s , c₁) →
  exec1 (putStrLn s)         >>
  method c₁ (put arg) >>= λ{ (_ , c₂) →
  method c₂ get       >>= λ{ (s' , c₃) →
  exec1 (putStrLn s')
  }}}

main : NativeIO Unit
main = translateIOConsole (program "hello")
