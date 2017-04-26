{-# OPTIONS --postfix-projections #-}

module src.StateSizedIO.cellStateDependent where

open import Data.Product
open import Data.String.Base

{-
open import SizedIO.Object
open import SizedIO.ConsoleObject
-}

open import src.SizedIO.Console hiding (main)

open import src.SizedIO.Base

open import src.NativeIO

open import src.StateSizedIO.Object
open import src.StateSizedIO.IOObject


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

putGen : {A : Set} → {i : CellStateˢ} → A → CellMethodˢ A i
putGen {i = empty} = put
putGen {i = full} = put


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


-- UNSIZED Version, without IO
mutual
   cellPempty' : ∀{A} → Objectˢ (CellInterfaceˢ A) empty
   cellPempty' .objectMethod (put a)     =  (_ , cellPfull' a)

   cellPfull' : ∀{A} → A → Objectˢ (CellInterfaceˢ A) full
   cellPfull' a .objectMethod get         = (a , cellPfull' a)
   cellPfull' a .objectMethod (put a')  = (_ , cellPfull' a')
