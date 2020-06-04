{-# OPTIONS --postfix-projections #-}

module StateSized.StackStateDependent where

open import Data.Product
open import Function
open import Data.String.Base as Str
open import Data.Nat.Base as N
open import Data.Vec as Vec using (Vec; []; _∷_; head; tail)

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Product.Pointwise

open import NativeIO

open import SizedIO.Base
open import SizedIO.Console hiding (main)

open import StateSizedIO.GUI.BaseStateDependent
open import StateSizedIO.Object
open import StateSizedIO.IOObject


open import Size

StackStateˢ = ℕ

data StackMethodˢ (A : Set) : StackStateˢ → Set where
  push : {n : StackStateˢ} → A → StackMethodˢ A n
  pop  : {n : StackStateˢ} → StackMethodˢ A (suc n)

StackResultˢ : (A : Set) → (s : StackStateˢ) → StackMethodˢ A s → Set
StackResultˢ A .n (push { n  } x₁)  = Unit
StackResultˢ A (suc .n)  (pop {n} ) = A

nˢ : (A : Set) → (s : StackStateˢ) → (m : StackMethodˢ A s) → (r : StackResultˢ A s m) → StackStateˢ
nˢ A .n (push { n } x)     r = suc n
nˢ A (suc .n) (pop  { n }) r = n


StackInterfaceˢ : (A : Set) → Interfaceˢ
StackInterfaceˢ A .Stateˢ  = StackStateˢ
StackInterfaceˢ A .Methodˢ = StackMethodˢ A
StackInterfaceˢ A .Resultˢ = StackResultˢ A
StackInterfaceˢ A .nextˢ = nˢ A

stackP : ∀{n : ℕ} → (i : Size) → (v : Vec String n) → IOObjectˢ consoleI (StackInterfaceˢ String) i n
method (stackP { n }   i es)       {j} (push e) = return (_ , stackP j (e ∷ es))
method (stackP {suc n} i (x ∷ xs)){j} pop      = return (x , stackP j xs)



-- UNSIZED Version, without IO

stackP' : ∀{n : ℕ} → (v : Vec String n) → Objectˢ (StackInterfaceˢ String) n
stackP' es .objectMethod (push e) = (_ , stackP' (e ∷ es))
stackP' (x ∷ xs) .objectMethod pop = x , stackP' xs



stackO : ∀{E : Set} {n : ℕ} (v : Vec E n) → Objectˢ (StackInterfaceˢ E) n
objectMethod (stackO es)      (push e) = _ , stackO (e ∷ es)
objectMethod (stackO (e ∷ es)) pop      = e , stackO es

stackF : ∀{E : Set} (n : ℕ) (f : ℕ → E) → Objectˢ (StackInterfaceˢ E) n
objectMethod (stackF n f) (push x) = _ , stackF (suc n)
  \{ zero → x
   ; (suc m) → f m
   }
objectMethod (stackF (suc n) f) pop = (f zero) , stackF n (f  ∘ suc)

tabulate : ∀{E : Set} (n : ℕ) (f : ℕ → E) → Vec E n
tabulate zero    f = []
tabulate (suc n) f = f zero ∷ tabulate n λ m → f (suc m)

module _ {E : Set} where
  private
    I = StackInterfaceˢ E
    S = Stateˢ I
    O = Objectˢ I
  open Bisim I

  _≡×≅'_ : ∀{s} → (o o' : E × O s) → Set
  _≡×≅'_ = _≡_ ×-Rel _≅_

  Eq×Bisim : ∀ (s : S) → (o o' : E × O s) → Set
  Eq×Bisim s = _≡_ ×-Rel _≅_

  pop-after-push : ∀{n}{v : Vec E n} (e : E) (let stack = stackO v) →
     (objectMethod stack (push e) ▹   λ { (_ , stack₁) →
      objectMethod stack₁ pop     ▹   λ { (e₁ , stack₂) →
      ( e₁ , stack₂ )  }})
    ≡×≅' (e , stack)
  pop-after-push e = refl , refl≅ _


  push-after-pop : ∀{n}{v : Vec E n} (e : E) (let stack = stackO (e ∷ v)) →
     (objectMethod stack  pop       ▹  λ { (e₁ , stack₁) →
      objectMethod stack₁ (push e₁) ▹  λ { (_  , stack₂) →
      stack₂ }})
     ≅ stack
  push-after-pop e = refl≅ _


  -- The implementations of stacks with either vectors or functions are bisimilar.

  impl-bisim : ∀{n : ℕ} {f : ℕ → E} (v : Vec E n) (p : tabulate n f ≡ v)
    → stackF n f ≅ stackO v

  bisimMethod (impl-bisim v       p) (push e) =
    bisim (impl-bisim (e ∷ v) (cong (_∷_ e) p))

  bisimMethod (impl-bisim (x ∷ v) p) pop rewrite cong head p =
    bisim (impl-bisim v (cong tail p))

program : IOConsole ∞ Unit
program = 
  exec getLine                λ str₀ →
  method s₀ (push str₀) >>= λ{ (_ , s₁) →            -- empty
  exec getLine                λ   str₁ →
  method s₁ (push str₁) >>= λ{ (_ , s₂) →            -- full
  method s₂ pop         >>= λ{ (str₂ , s₃) →
  exec (putStrLn ("first pop: " Str.++ str₂)  ) λ _ →
  exec getLine                λ   str₃ →
  method s₃ (push str₃) >>= λ{ (_ , s₄) →
  method s₄ pop         >>= λ{ (str₄ , s₅) →
  exec (putStrLn ("second pop: " Str.++ str₄)  ) λ _ →
  method s₅ pop         >>= λ{ (str₅ , s₅) →
  exec (putStrLn ("third  pop: " Str.++ str₅)  ) λ _ →
  return unit
  }}}}}}
  where
    s₀ = stackP ∞ []

main : NativeIO Unit
main = translateIOConsole program

