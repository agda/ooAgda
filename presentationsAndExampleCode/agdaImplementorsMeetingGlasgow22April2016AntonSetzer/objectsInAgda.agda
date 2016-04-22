module objectsInAgda where

open import Data.Product
open import interactiveProgramsAgda hiding (main)
open import NativeIO
open import Data.String.Base


record Interface  :  Set₁ where
  field  Method   :  Set
         Result   :  (m : Method) → Set

open Interface public

record Object (I : Interface) : Set where
  coinductive
  field objectMethod : (m : Method I) → Result I m × Object I

open Object public
open import Size


record IOObject (Iᵢₒ : IOInterface) (I : Interface) (i : Size) : Set where
  coinductive
  field method : ∀{j : Size< i} (m : Method I)
                   → IO Iᵢₒ ∞ (Result I m × IOObject Iᵢₒ I j)

open IOObject public

{- Example Cell -}

data CellMethod A : Set where
    get  :  CellMethod A
    put  :  A → CellMethod A

CellResult             :  ∀{A} → CellMethod A → Set
CellResult   {A} get   =  A
CellResult   (put _)   =  Unit

cellI                  :  (A : Set) → Interface
Method    (cellI A)    =  CellMethod A
Result    (cellI A) m  =  CellResult m


{- A cell as an Object -}

Cell : Set → Set
Cell A = Object (cellI A)

cell : {A : Set} → A → Cell A
objectMethod (cell a) get       = a    , cell a
objectMethod (cell a) (put a')  = unit , cell a'




{- A cell as an IOObject -}

CellC : (i : Size) → Set
CellC = IOObject ConsoleInterface (cellI String)


simpleCell : ∀{i} (s : String) → CellC i
force (method (simpleCell s)  get) =
  do' (putStrLn ("getting (" ++ s ++ ")")) λ _ →
  return (s , simpleCell s)
force (method (simpleCell _) (put s)) =
  do' (putStrLn ("putting (" ++ s ++ ")")) λ _ →
  return (_ , simpleCell s)


program : ∀{i} → CellC ∞  → IO ConsoleInterface i Unit
force (program c) =
  do' getLine          λ s →
  method c (put s)    >>= λ{ (_ , c) →
  method c get        >>= λ{ (s' , c) →
  do (putStrLn s')     λ _ →
  program c }}


main : NativeIO Unit
main = translateIOConsole (program (simpleCell "Start"))

