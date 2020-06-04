module Sized.StatefulCell where

open import Data.Product
open import Data.String.Base

open import SizedIO.Object
open import SizedIO.IOObject
open import SizedIO.ConsoleObject

open import SizedIO.Console hiding (main)

open import NativeIO

open import Size

--open import StateSizedIO.Base

data CellState#  : Set where
  empty full  : CellState#

data CellMethodEmpty A : Set where
    put : A → CellMethodEmpty A

data CellMethodFull A : Set where
    get : CellMethodFull A
    put : A → CellMethodFull A

CellMethod# : ∀{A} → CellState# → Set
CellMethod#{A} empty = CellMethodEmpty A
CellMethod#{A} full = CellMethodFull A


CellResultFull : ∀{A} → CellMethodFull A → Set
CellResultFull {A} get = A
CellResultFull (put _) = Unit

CellResultEmpty : ∀{A} → CellMethodEmpty A → Set
CellResultEmpty (put _) = Unit


CellResult# : ∀{A} → (s : CellState#) → CellMethod#{A} s → Set
CellResult#{A} empty = CellResultEmpty{A}
CellResult#{A} full = CellResultFull{A}


n# : ∀{A} → (s : CellState#) → (c : CellMethod#{A} s) → (CellResult# s c) → CellState#
n# empty (put x) unit = full
n# full get z = full
n# full (put x) unit = full
