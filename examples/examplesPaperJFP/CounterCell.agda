module examplesPaperJFP.CounterCell where

open import Data.Product
open import Data.Nat.Base
open import Data.Nat.Show
open import Data.String.Base using (String; _++_)

open import Size

-- open import NativeIO

-- open import SizedIO.Base
-- open import SizedIO.Object
-- open import SizedIO.IOObject
-- open import SizedIO.ConsoleObject
-- open import SizedIO.Console hiding (main)

open import examplesPaperJFP.NativeIOSafe

open import examplesPaperJFP.ConsoleInterface
open import examplesPaperJFP.Console hiding (main)
open import examplesPaperJFP.Object using (Interface; Method; Result; CellMethod; get; put; CellResult; cellJ)
open import examplesPaperJFP.Sized hiding (program; main)

data CounterMethod A : Set where
  super  :  (m : CellMethod A) → CounterMethod A
  stats  :  CounterMethod A

pattern getᶜ    = super get
pattern putᶜ x  = super (put x)

statsCellI : (A : Set) → Interface
Method  (statsCellI A)            =  CounterMethod A
Result  (statsCellI A) (super m)  =  Result (cellJ A) m
Result  (statsCellI A) stats      =  Unit

CounterC : (i : Size) → Set
CounterC = IOObject ConsoleInterface (statsCellI String)

counterCell : ∀{i} (c : CellC i) (ngets nputs : ℕ) → CounterC i

method (counterCell c ngets nputs) getᶜ =
  method c get                                >>= λ { (s , c′) →
  return (s , counterCell c′ (1 + ngets) nputs)  }

method (counterCell c ngets nputs) (putᶜ x) =
  method c (put x)                            >>= λ { (_ , c′) →
  return (unit , counterCell c′ ngets (1 + nputs))  }

method (counterCell c ngets nputs) stats =
  do' (putStrLn ("Counted "
    ++ show ngets ++ " calls to get and "
    ++ show nputs ++ " calls to put."))       λ _ →
  return (unit , counterCell c ngets nputs)

program : String → IO ConsoleInterface ∞ Unit
program arg =
  let c₀ = counterCell (simpleCell "Start") 0 0 in
  method c₀ getᶜ               >>= λ{ (s   , c₁) →
  do' (putStrLn s)              λ _ →
  method c₁ (putᶜ arg)         >>= λ{ (_        , c₂) →
  method c₂ getᶜ               >>= λ{ (s′  , c₃) →
  do' (putStrLn s′)             λ _ →
  method c₃ (putᶜ "Over!")     >>= λ{ (_ , c₄) →
  method c₄ stats              >>= λ{ (_ , c₅) →
  return unit                  }}}}}

main : NativeIO Unit
main = translateIO translateIOConsoleLocal (program "Hello")
