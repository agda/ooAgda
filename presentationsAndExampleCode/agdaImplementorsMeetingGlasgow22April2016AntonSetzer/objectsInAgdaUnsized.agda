module objectsInAgdaUnsized where

open import Data.Product
open import interactiveProgramsAgdaUnsized hiding (main)
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

CellC : Set
CellC = IOObject ConsoleInterface (cellI String)


simpleCell : (s : String) → CellC
force (method (simpleCell s) get) =
  do' (putStrLn ("getting (" ++ s ++ ")")) λ _ →
  delay (return' (s , simpleCell s))
force (method (simpleCell s) (put x)) =
  do' (putStrLn ("putting (" ++ x ++ ")")) λ _ →
  delay (return' (_ , simpleCell x))

{-# TERMINATING #-}

program : CellC → IOConsole Unit
force (program c₁) =
  do' getLine          λ s →
  method c₁ (put s)    >>= λ{ (_  , c₂) →
  method c₂ get        >>= λ{ (s' , c₃) →
  do (putStrLn s')     λ _ →
  (program c₃)}}

main : NativeIO Unit
main = translateIOConsole (program (simpleCell "Start"))
