module src.heap.library where


open import Relation.Nullary
open import Data.Nat hiding (_≟_) renaming (_⊔_ to _⊔n_)
open import Relation.Binary.Core

open import Data.Fin hiding (lift)
open import Data.Empty
open import Data.Unit
open import Data.Maybe.Base
open import Data.Product renaming (proj₁ to pr₁; proj₂ to pr₂) hiding (_×_)
open import Level renaming (zero to lzero; suc to lsuc) hiding (lift)


--postulate TODO : ∀ {a} {A : Set a} → A

isNull : ∀ {a} {A : Set a} → Maybe A → Set
isNull (just _) = ⊥
isNull nothing = ⊤

inj : ∀ {a b} {A : Set a} {B : A → Set b} {a' : A} (b' : B a') → Σ A B
inj{a' = a'} b' = a' , b'


data _×_  {σ τ} (A : Set σ) (B : Set τ) : Set (σ ⊔ τ) where
    _,,_ : A → B → A × B

proj₁ : {σ τ : Level} {A : Set σ} {B : Set τ} →  A × B → A
proj₁ (a ,, b) = a

proj₂ : {σ τ : Level} {A : Set σ} {B : Set τ} →  A × B → B
proj₂ (a ,, b) = b


finSucInj¬ : {n : ℕ} → (q q' : Fin n) → ¬ (_≡_ {lzero} {Fin (suc n)} (suc q)  (suc q')) → ¬ (q ≡ q')
finSucInj¬ zero .zero ¬sqsq' refl = ¬sqsq' refl
finSucInj¬ (suc q) .(suc q) ¬sqsq' refl = ¬sqsq' refl

trans≡ : {A : Set} {a a' a'' : A} → a ≡ a' → a' ≡ a'' → a ≡ a''
trans≡ refl refl = refl

injsuc : {n : ℕ} {k l : Fin n} → ¬ (_≡_ {lzero} {Fin (suc n)} (suc k) (suc l)) → ¬ k ≡ l
injsuc ¬snsm refl = ¬snsm refl

injsuc2 : {n : ℕ} {k l : Fin n} → (_≡_ {lzero} {Fin (suc n)} (suc k) (suc l)) → k ≡ l
injsuc2 refl = refl

zero¬=sucFin : {n : ℕ} → (l : Fin n) → ¬ (_≡_ {lzero} {Fin (suc n)} zero  (suc l))
zero¬=sucFin l ()

sym : {A : Set} {a a' : A} (aa' : a ≡ a') → (a' ≡ a)
sym refl = refl

sym' : {A : Set} {a a' : A} (aa' : ¬ (a ≡ a')) → ¬ (a' ≡ a)
sym'  aa' a'a = aa' (sym a'a)
