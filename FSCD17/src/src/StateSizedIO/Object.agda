module src.StateSizedIO.Object where

open import Data.Product
open import src.StateSizedIO.Base public

module _ (I : Interfaceˢ)(let S = Stateˢ I) (let M = Methodˢ I)
         (let R = Resultˢ I) (let next = nextˢ I) where
  -- A simple object just returns for a method the response
  -- and the object itself
  record Objectˢ (s : S) : Set where
    coinductive
    field
      objectMethod : (m : M s) → Σ[ r ∈ R s m ] Objectˢ (next s m r)

  open Objectˢ public



_▹_  : {A : Set } → { B : Set } →  A → (A → B) → B
a ▹ f = f a


-- Bisimilation for Objectˢ

module Bisim (I : Interfaceˢ)
  (let S    = Stateˢ  I)
  (let M    = Methodˢ I)
  (let R    = Resultˢ I)
  (let next = nextˢ   I)
  (let O = Objectˢ I)
  where

    mutual

      record _≅_ {s : S} (o o' : O s) : Set where
        coinductive
        field bisimMethod : (m : M s) → objectMethod o m ≡×≅ objectMethod o' m

      data _≡×≅_ {s m} : (p p' :  Σ[ r ∈ R s m ] O (next s m r)) → Set where
        bisim : ∀{r} (let s' = next s m r) {o o' : O s'} (p : o ≅ o')
              → (r , o) ≡×≅ (r , o')

    open _≅_ public

    refl≅ : ∀{s} (o : O s) → o ≅ o
    bisimMethod (refl≅ o) m = bisim (refl≅ (proj₂ (objectMethod o m)))
