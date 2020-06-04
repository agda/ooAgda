module examplesPaperJFP.StatefulObject where

open import Data.Product
open import Data.String.Base as Str
open import Data.Nat.Base as N
open import Data.Vec as Vec using (Vec; []; _∷_; head; tail)

open import SizedIO.Console hiding (main)
open import Size

open import NativeIO

open import SizedIO.Base


StackStateˢ = ℕ

record Interfaceˢ : Set₁ where
  field  Stateˢ    :  Set
         Methodˢ   :  (s : Stateˢ)  →  Set
         Resultˢ   :  (s : Stateˢ)  →  (m : Methodˢ s)  →  Set
         nextˢ     :  (s : Stateˢ)  →  (m : Methodˢ s)  →  (r : Resultˢ s m) → Stateˢ

open Interfaceˢ public

data StackMethodˢ (A : Set) : (n : StackStateˢ) → Set where
  push  :  ∀ {n}  →  A  →  StackMethodˢ A n
  pop   :  ∀ {n}        →  StackMethodˢ A (suc n)

StackResultˢ                      :  (A : Set) → (s : StackStateˢ) → StackMethodˢ A s → Set
StackResultˢ A _  (push _)  =  Unit
StackResultˢ A _  pop       =  A


stackNextˢ  :  ∀ A n (m : StackMethodˢ A n) (r : StackResultˢ A n m) →  StackStateˢ
stackNextˢ _  n        (push _)  _  =  suc n
stackNextˢ _  (suc n)  pop       _  =  n

StackInterfaceˢ : (A : Set)  →  Interfaceˢ
Stateˢ   (StackInterfaceˢ A)  =  StackStateˢ
Methodˢ  (StackInterfaceˢ A)  =  StackMethodˢ A
Resultˢ  (StackInterfaceˢ A)  =  StackResultˢ A
nextˢ    (StackInterfaceˢ A)  =  stackNextˢ A

record Objectˢ (I : Interfaceˢ) (s : Stateˢ I) : Set where
  coinductive
  field objectMethod :  (m : Methodˢ I s) →
                        Σ[ r ∈ Resultˢ I s m ] Objectˢ I (nextˢ I s m r)
open Objectˢ public

record IOObjectˢ (Iᵢₒ : IOInterface) (I : Interfaceˢ) (s : Stateˢ I) : Set where
  coinductive
  field method :  (m : Methodˢ I s) →
                  IO Iᵢₒ ∞ (Σ[ r ∈ Resultˢ I s m ] IOObjectˢ Iᵢₒ I (nextˢ I s m r))
open IOObjectˢ public

stack  :  ∀{A}{n : ℕ} (as : Vec A n) →  Objectˢ (StackInterfaceˢ A) n
objectMethod (stack as)        (push a)  =  unit  ,  stack (a ∷ as)
objectMethod (stack (a ∷ as))  pop       =  a     ,  stack as
