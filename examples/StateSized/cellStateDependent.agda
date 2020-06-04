{-# OPTIONS --postfix-projections #-}

module StateSized.cellStateDependent where

open import Data.Product
open import Data.String.Base

{-
open import SizedIO.Object
open import SizedIO.ConsoleObject
-}

open import SizedIO.Console hiding (main)

open import SizedIO.Base

open import NativeIO

open import StateSizedIO.Object
open import StateSizedIO.IOObject


open import Size
open import StateSizedIO.cellStateDependent


{- I moved most into src/StateSizedIO/cellStateDependent.agda

now the code doesn't work
-}

-- Program is another program
program : IOConsole ∞ Unit
program =
  let c₀ = cellPempty ∞  in
  exec getLine            λ str →
  method c₀ (put str)    >>= λ{ (_ , c₁) →        -- empty
  method c₁ get          >>= λ{ (str₁ , c₂) →     -- full
  exec (putStrLn ("we got " ++ str₁))    λ _ →
  exec (putStrLn ("Second Round"))    λ _ →
  exec getLine            λ str₂ →
  method c₂ (put str₂)    >>= λ{ (_ , c₃) →
  method c₃ get          >>= λ{ (str₃ , c₄) →
  exec (putStrLn ("we got " ++ str₃)  ) λ _ →
  return unit
  }}}}

main : NativeIO Unit
main = translateIOConsole program



-- cellP is constructor for the consoleObject for interface (cellI String)
{-
cellPˢ : ∀{i} → CellCˢ i
force (method cellPˢ (put x)) = {!!}
-}

{-
cellP : ∀{i} (s : String) → CellC i
force (method (cellP s) get) =
  exec' (putStrLn ("getting (" ++ s ++ ")")) λ _ →
  return (s , cellP s)
force (method (cellP s) (put x)) =
  exec' (putStrLn ("putting (" ++ x ++ ")")) λ _ →
  return (_ , (cellP x))
-}


{-
-- cellI is the interface of the object of a simple cell
cellI : (A : Set) → Interfaceˢ
Method  (cellI A)    =  CellMethodˢ A
Result  (cellI A) m  =  CellResultˢ m

-- cellC is the type of consoleObjects with interface (cellI String)
CellC : (i : Size) → Set
CellC i = ConsoleObject i (cellI String)
-}
{-
-- cellO is a program for a simple cell which
-- when get is called writes "getting s" for the string s of the object
-- and when putting s writes "putting s" for the string

-- cellP is constructor for the consoleObject for interface (cellI String)
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
  exec1 (putStrLn s')        }}}

main : NativeIO Unit
main = translateIOConsole (program "hello")
-}
