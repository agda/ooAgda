module StateSizedIO.GUI.BaseStateDependent where

open import Size renaming (Size to AgdaSize)
open import NativeIO
open import Function
open import Agda.Primitive
open import Level using (_⊔_) renaming (suc to lsuc)


record IOInterfaceˢ {γ ρ μ} : Set (lsuc (γ ⊔ ρ ⊔ μ )) where
  field
    Stateˢ    : Set γ 
    Commandˢ  : Stateˢ → Set ρ
    Responseˢ : (s : Stateˢ) → Commandˢ s → Set μ 
    nextˢ     : (s : Stateˢ) → (c : Commandˢ s) → Responseˢ s c → Stateˢ
open IOInterfaceˢ public

module _  {α γ ρ μ}(i   : IOInterfaceˢ {γ} {ρ} {μ} )  
                                (let S = Stateˢ i)     (let C  = Commandˢ i)
                                (let  R  = Responseˢ i) (let next = nextˢ i)

  where
    mutual
      record IOˢ (i : AgdaSize)  (A : S → Set α) (s : S) : Set (lsuc (α ⊔ γ ⊔ ρ ⊔ μ )) where
        coinductive
        constructor delay
        field
          forceˢ : {j : Size< i} → IOˢ' j A s
  
      data IOˢ' (i : AgdaSize)  (A : S → Set α) : S → Set (lsuc (α ⊔ γ ⊔ ρ ⊔ μ )) where
        doˢ'     : {s : S} → (c : C s) → (f : (r : R s c) → IOˢ i A (next s c r) ) 
                   → IOˢ' i A s
        returnˢ' : {s : S} → (a : A s) → IOˢ' i A s

    data IOˢ+ (i : AgdaSize)  (A : S → Set α ) : S → Set (lsuc (α ⊔ γ ⊔ ρ ⊔ μ )) where
      doˢ' : {s : S} → (c : C s) (f : (r : R s c) → IOˢ i A  (next s c r)) 
            → IOˢ+ i A s

open IOˢ public

 
module _  {α γ ρ μ}{I   : IOInterfaceˢ {γ} {ρ} {μ}}     
                   (let S = Stateˢ I)     (let C  = Commandˢ I)
                   (let  R  = Responseˢ I) (let next = nextˢ I) where
  returnˢ : ∀{i}{A : S → Set α} {s : S} (a : A s) → IOˢ  I i A s
  forceˢ (returnˢ a) = returnˢ' a

  doˢ  : ∀{i}{A : S → Set α} {s : S} (c : C s) 
         (f : (r : R s c) → IOˢ I i A (next s c r)) 
         → IOˢ I i A s
  forceˢ (doˢ c f) = doˢ' c f


module _  {γ ρ}{I   : IOInterfaceˢ {γ} {ρ} {lzero}}     
                (let S = Stateˢ I)     (let C  = Commandˢ I)
                (let  R  = Responseˢ I) (let next = nextˢ I) where
  {-# NON_TERMINATING #-}

  translateIOˢ : ∀{A : Set }{s : S}
    →  (translateLocal : (s : S) → (c : C s) → NativeIO (R s c))
    →  IOˢ I ∞ (λ s → A) s
    →  NativeIO A
  translateIOˢ {A} {s} translateLocal p = case (forceˢ p {_}) of
    λ{ (doˢ' {.s} c f)    → (translateLocal s c)     native>>= λ r →
                             translateIOˢ translateLocal (f r)
     ; (returnˢ' a) → nativeReturn a
     }


