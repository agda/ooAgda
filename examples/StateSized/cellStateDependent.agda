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

data CellStateˢ  : Set where
  empty full  : CellStateˢ

data CellMethodEmpty A : Set where
    put : A → CellMethodEmpty A

data CellMethodFull A : Set where
    get : CellMethodFull A
    put : A → CellMethodFull A

CellMethodˢ : (A : Set) → CellStateˢ → Set
CellMethodˢ A empty = CellMethodEmpty A
CellMethodˢ A full = CellMethodFull A


CellResultFull : ∀{A} → CellMethodFull A → Set
CellResultFull {A} get = A
CellResultFull (put _) = Unit

CellResultEmpty : ∀{A} → CellMethodEmpty A → Set
CellResultEmpty (put _) = Unit


CellResultˢ : (A : Set) → (s : CellStateˢ) → CellMethodˢ A s → Set
CellResultˢ A empty = CellResultEmpty{A}
CellResultˢ A full = CellResultFull{A}


nˢ : ∀{A} → (s : CellStateˢ) → (c : CellMethodˢ A s) → (CellResultˢ A s c) → CellStateˢ
nˢ _ _ _ = full

CellInterfaceˢ : (A : Set) → Interfaceˢ
Stateˢ (CellInterfaceˢ A)  = CellStateˢ
Methodˢ (CellInterfaceˢ A)  = CellMethodˢ A
Resultˢ (CellInterfaceˢ A)  = CellResultˢ A
nextˢ (CellInterfaceˢ A)  = nˢ

mutual
   cellPempty : (i : Size) → IOObject consoleI (CellInterfaceˢ String) i empty
   method (cellPempty i) {j} (put str) = do (putStrLn ("put (" ++ str ++ ")")) λ _ →
                                         return (unit , cellPfull j str)

   cellPfull : (i : Size) → (str : String) → IOObject consoleI (CellInterfaceˢ String) i full
   method (cellPfull i str) {j} get        = do (putStrLn ("get (" ++ str ++ ")")) λ _ →
                                             return (str , cellPfull j str)
   method (cellPfull i str) {j} (put str') = do (putStrLn ("put (" ++ str' ++ ")")) λ _ →
                                             return (unit , cellPfull j str')



-- Program is another program
program : IOConsole ∞ Unit
program =
  let c₀ = cellPempty ∞  in
  do getLine            λ str →
  method c₀ (put str)    >>= λ{ (_ , c₁) →        -- empty
  method c₁ get          >>= λ{ (str₁ , c₂) →     -- full
  do (putStrLn ("we got " ++ str₁))    λ _ →
  do (putStrLn ("Second Round"))    λ _ →
  do getLine            λ str₂ →
  method c₂ (put str₂)    >>= λ{ (_ , c₃) →
  method c₃ get          >>= λ{ (str₃ , c₄) →
  do (putStrLn ("we got " ++ str₃)  ) λ _ →
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
  do' (putStrLn ("getting (" ++ s ++ ")")) λ _ →
  return (s , cellP s)
force (method (cellP s) (put x)) =
  do' (putStrLn ("putting (" ++ x ++ ")")) λ _ →
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
-}
