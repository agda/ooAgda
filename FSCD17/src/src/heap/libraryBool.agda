module src.heap.libraryBool where

open import Data.Bool.Base
open import Data.Bool
open import Data.Unit hiding (_≤_; _≤?_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Level

ifthenelseLemma1 : ∀ {σ} {τ} {α} → (A : Set σ ) → (P : A → Set τ )  → (Q : Set α)
                   → (b : Bool) → (a a' : A)
                   → (T b → P a → Q)
                   → (¬ (T b)  → P a' → Q)
                   → P (if b then a else a') → Q
ifthenelseLemma1 A P Q true a a' p p' p'' = p tt p''
ifthenelseLemma1 A P Q false a a' p p' p'' = p' (λ x → x) p''



ifthenelseLemma2 : ∀ {σ} {τ} →  (A : Set σ ) → (P : A → Set τ )
                   → (b : Bool) → (a a' : A)
                   → (T b → P a)
                   → (¬ (T b)  → P a')
                   → P (if b then a else a')
ifthenelseLemma2 A P true a a' p p' = p tt
ifthenelseLemma2 A P false a a' p p' = p' (λ x → x)


ifthenelseLemma3 : ∀ {σ} {τ} →  (A : Set σ ) → (P : A → Set τ )
                   → (b : Bool) → (a a' : A)
                   → ¬ (T b)
                   → P a'
                   → P (if b then a else a')
ifthenelseLemma3 A P true a a' p q = ⊥-elim (p tt )
ifthenelseLemma3 A P false a a' p q = q

ifthenelseLemma3' : ∀ {σ} {τ} →  (A : Set σ ) → (P : A → Set τ )
                   → (b : Bool) → (a a' : A)
                   → (T b)
                   → P a
                   → P (if b then a else a')
ifthenelseLemma3' A P true a a' p q = q
ifthenelseLemma3' A P false a a' p q = ⊥-elim p


boolLem1 : (P : Bool → Set) → P true → P false → (b : Bool) → P b
boolLem1 P pt pf false = pf
boolLem1 P pt pf true = pt

boolLem2 :  ∀ {σ} (P : Bool → Set σ) → P true → (b : Bool) → T b → P b
boolLem2 P pt false ()
boolLem2 P pt true tb = pt


boolLem2double : (P : Bool → Bool → Set) → P true true → (b b' : Bool)
                 → T b → T b' → P b b'
boolLem2double P pt false b' () tb'
boolLem2double P pt true false tb ()
boolLem2double P pt true true tb tb' = pt


boolLem3 : (P : Bool → Set) → P false → (b : Bool) → ¬ (T b) → P b
boolLem3 P pf false fb = pf
boolLem3 P pf true fb = ⊥-elim (fb tt)


σ : (a : Bool) → (b : T a →  Bool) → Bool
σ false b = false
σ true b = b tt

infix 2 σ-syntax

σ-syntax : (a : Bool) → (b : T a →  Bool) → Bool
σ-syntax = σ

syntax σ-syntax A (λ x → B) = σ[ x ∈ A ] B

proj₁σ : {a : Bool} → {b : T a →  Bool} → T (σ a b) → T a
proj₁σ {false} ()
proj₁σ {true} p = tt

proj₂σ : {a : Bool} → {b : T a →  Bool} → (p : T (σ a b)) → T (b (proj₁σ p))
proj₂σ {false} ()
proj₂σ {true} p = p

proj₁∧  : {a b :  Bool} → T (a ∧  b) → T a
proj₁∧ {false} ()
proj₁∧ {true} p = tt

proj₂∧  : {a b : Bool} → T (a ∧  b) → T b
proj₂∧ {false} ()
proj₂∧ {true} p = p

T∧  : {a b : Bool} → T a → T b → T (a ∧  b)
T∧ {false}{_} ()
T∧ {_}{false} _ ()
T∧ {true}{true} = λ _ _ → tt

proj₂∧T∧ : {a b : Bool} → (ta : T a) → (tb : T b) → (proj₂∧{a}{b} (T∧{a}{b} ta tb)) ≡ tb
proj₂∧T∧ {_} {false} ta tb = ⊥-elim tb
proj₂∧T∧ {false} {_} ta tb = ⊥-elim ta
proj₂∧T∧ {true} {true} tt tt = refl



boolNegLem : {b : Bool} → ¬ (T  b) → b ≡ false
boolNegLem {false} p = refl
boolNegLem {true} p = ⊥-elim (p tt )
