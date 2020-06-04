module examplesPaperJFP.safeFibStackMachineObjectOriented where

open import Data.Nat
open import Data.List
open import Data.Vec
open import Data.Sum
open import Data.Fin renaming (_+_ to _+f_)
open import Data.Product
open import examplesPaperJFP.StatefulObject
open import examplesPaperJFP.StackBisim

open import examplesPaperJFP.triangleRightOperator



{- Object based version of safe stack
   it is essentially the last part of safeFibStackMachine.agda
   with the names simplified -}


{- the state is what we are computing right now:
   fib n  menas we need to compute fib n
   val k  means we have computed   the value k
-}



data FibState : Set where
  fib  :  ℕ  →  FibState
  val  :  ℕ  →  FibState

data FibStackEl : Set where
  _+•     :  ℕ  →  FibStackEl
  •+fib_  :  ℕ  →  FibStackEl

FibStack : ℕ → Set
FibStack = Objectˢ (StackInterfaceˢ FibStackEl)

FibStackmachine : Set
FibStackmachine = Σ[ n ∈ ℕ ] (FibState × FibStack n)

reduce : FibStackmachine →  FibStackmachine ⊎ ℕ
reduce  (n      ,  fib 0             ,  stack)  =  inj₁ (n  ,  val 1  ,  stack)
reduce  (n      ,  fib 1             ,  stack)  =  inj₁ (n  ,  val 1  ,  stack)
reduce  (n      ,  fib (suc (suc m)) ,  stack)  =
        objectMethod stack (push (•+fib m))   ▹   λ  {  (_ , stack₁) →
        inj₁ ( suc n , fib (suc m) , stack₁)         }
reduce  (0      ,  val k             ,  stack)  =   inj₂ k
reduce  (suc n  ,  val k             ,  stack)  =
        objectMethod stack pop                ▹   λ  {  (k′ +•    , stack₁) →
        inj₁ (n , val (k′ + k) , stack₁)
                                                     ;  (•+fib m  , stack₁) →
        objectMethod stack₁ (push (k +•))     ▹   λ  {  (_ , stack₂) →
        inj₁ (suc n , fib m , stack₂)                }}

iter : (m : ℕ) → FibStackmachine →  FibStackmachine ⊎ ℕ
iter  0        s  =  inj₁ s
iter  (suc n)  s  with  reduce s
... |  inj₁ s′    =  iter n s′
... |  inj₂ m     =  inj₂ m

computeFib : ℕ → ℕ →  FibStackmachine ⊎ ℕ
computeFib n m = iter n (0 , fib m , stack [])

fibO0 :  FibStackmachine ⊎ ℕ
fibO0 = computeFib 2 0

-- evaluates to inj₂ 1

fibO1 :  FibStackmachine ⊎ ℕ
fibO1 = computeFib 2 1
-- evaluates to inj₂ 1

fibO2 :  FibStackmachine ⊎ ℕ
fibO2 = computeFib 10 2
-- evaluates to inj₂ 2

fibO3 :  FibStackmachine ⊎ ℕ
fibO3 = computeFib 14 3
-- evaluates to inj₂ 3

fibO4 :  FibStackmachine ⊎ ℕ
fibO4 = computeFib 30 4
-- evaluates to inj₂ 5

fibO5 :  FibStackmachine ⊎ ℕ
fibO5 = computeFib 30 5
-- evaluates to inj₂ 8

{-# TERMINATING #-}
computeFibRec : FibStackmachine → ℕ
computeFibRec s with reduce s
... | inj₁ s′   = computeFibRec s′
... | inj₂ k    = k


fibUsingStack : ℕ → ℕ
fibUsingStack m = computeFibRec (0 , fib m , stack [])


test : List ℕ
test = fibUsingStack 0 ∷ fibUsingStack 1 ∷ fibUsingStack 2 ∷ fibUsingStack 3 ∷ fibUsingStack 4 ∷ fibUsingStack 5 ∷ fibUsingStack 6  ∷ []

testExpected : List ℕ
testExpected = 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ []
