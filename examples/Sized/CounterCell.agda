module Sized.CounterCell where

open import Data.Product
open import Data.Nat.Base
open import Data.Nat.Show
open import Data.String.Base using (String; _++_)

open import SizedIO.Object
open import SizedIO.IOObject

open import SizedIO.Base
open import SizedIO.Console hiding (main)
open import SizedIO.ConsoleObject

open import NativeIO

open import Sized.SimpleCell hiding (program; main)

open import Size

data CounterMethod A : Set where
  super : (m : CellMethod A) → CounterMethod A
  stats : CounterMethod A

pattern getᶜ   = super get
pattern putᶜ x = super (put x)

-- CounterResult : ∀{A} →

counterI : (A : Set) → Interface
Method (counterI A)           =  CounterMethod A
Result (counterI A) (super m) =  Result (cellJ A) m
Result (counterI A) stats     =  Unit


CounterC : (i : Size) → Set
CounterC i = ConsoleObject i (counterI String)

-- counterP is constructor for the consoleObject for interface counterI

counterP : ∀{i} (c : CellC i) (ngets nputs : ℕ) → CounterC i
method (counterP c ngets nputs) getᶜ =
  method c get                                >>= λ { (s , c') →
  return (s , counterP c' (1 + ngets) nputs)  }
method (counterP c ngets nputs) (putᶜ x) =
  method c (put x)                            >>= λ { (_ , c') →
  return (_ , counterP c' ngets (1 + nputs))  }
method (counterP c ngets nputs) stats =
  exec (putStrLn ("Counted "
    ++ show ngets ++ " calls to get and "
    ++ show nputs ++ " calls to put."))       λ _ →
  return (_ , counterP c ngets nputs)

program : String → IOConsole ∞ Unit
program arg =
  let c₀ = counterP (cellP "Start") 0 0 in
  method c₀ getᶜ               >>= λ{ (s   , c₁) →
  exec1 (putStrLn s)            >>
  method c₁ (putᶜ arg)         >>= λ{ (_        , c₂) →
  method c₂ getᶜ               >>= λ{ (s'  , c₃) →
  exec1 (putStrLn s')           >>
  method c₃ (putᶜ "Over!")     >>= λ{ (_ , c₄) →
  method c₄ stats              >>= λ{ (_ , c₅) →
  return _                     }}}}}

main : NativeIO Unit
main = translateIOConsole (program "Hello")

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
