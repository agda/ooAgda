module examplesPaperJFP.StackBisim where

open import Data.Product
open import Function
open import Data.Nat.Base as N
open import Data.Vec as Vec using (Vec; []; _∷_; head; tail)

open import Relation.Binary.PropositionalEquality

open import examplesPaperJFP.StatefulObject

module _ {S : Set} {M : S → Set}  {R : (s : S)  →  (m : M s)  →  Set} {next : (s : S)  →  (m : M s)  →  R s m → S} (let

  I  = record { Stateˢ = S; Methodˢ = M; Resultˢ = R; nextˢ = next }
 ) (let
  O = Objectˢ I

    ) where
module Bisim (I : Interfaceˢ)
  (let S    = Stateˢ  I)
  (let M    = Methodˢ I)
  (let R    = Resultˢ I)
  (let next = nextˢ I)
  (let O    = Objectˢ I) where

  data  ΣR     {A : Set} {B : A → Set} (R : ∀{a} (b b′ : B a) → Set)
               :  (p p′ : Σ[ a ∈ A ] B a) → Set
        where
        eqΣ    :  ∀{a}{b b′ : B a} → R b b′ → ΣR R (a , b) (a , b′)


  record _≅_ {s : S} (o o′ : O s) : Set where
    coinductive
    field  bisimMethod  :  (m : M s) →
                           ΣR (_≅_) (objectMethod o m) (objectMethod o′ m)

  open _≅_ public

  refl≅ :  ∀{s} (o : O s) → o ≅ o
  bisimMethod (refl≅ o) m  =  let  (r , o′) =  objectMethod o m
                              in   eqΣ (refl≅ o′)

module _ {E : Set} where
  private
    I = StackInterfaceˢ E
    S = Stateˢ I
    O = Objectˢ I
  open Bisim I

  pop-after-push : ∀{n} {v : Vec E n} {e : E} →
    let  st          =  stack v
         (_ , st₁)   =  objectMethod  st   (push e)
         (e₂ , st₂)  =  objectMethod  st₁  pop

    in   (e ≡ e₂) × (st ≅ st₂)

  pop-after-push = refl , refl≅ _


  push-after-pop : ∀{n} {v : Vec E n} {e : E} →
    let  st            =  stack (e ∷ v)
         (e₁  ,  st₁)  =  objectMethod st   pop
         (_   ,  st₂)  =  objectMethod st₁  (push e₁)

    in   st ≅ st₂

  push-after-pop = refl≅ _


  tabulate  :  ∀ (n : ℕ) (f : ℕ → E) → Vec E n
  tabulate  0        f  =  []
  tabulate  (suc n)  f  =  f 0 ∷ tabulate n (f ∘ suc)


  stackF : ∀ (n : ℕ) (f : ℕ → E) → Objectˢ (StackInterfaceˢ E) n
  objectMethod  (stackF  n        f) (push e)  =  _    ,  stackF (suc n) λ
    {  0        →  e
    ;  (suc m)  →  f m    }
  objectMethod  (stackF  (suc n)  f) pop       =  f 0  ,  stackF n (f  ∘ suc)


  impl-bisim : ∀{n f} v (p : tabulate n f ≡ v) → stackF n f ≅ stack v

  bisimMethod (impl-bisim v        p) (push e) =
    eqΣ (impl-bisim (e ∷ v)  (cong (_∷_ e)  p))

  bisimMethod (impl-bisim (e ∷ v)  p) pop rewrite cong head p =
    eqΣ (impl-bisim v        (cong tail     p))
