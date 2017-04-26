--@PREFIX@StateSizedRObject

module src.StateSizedIO.RObject where

open import Data.Product
open import src.StateSizedIO.Base public
{-
--  This definition was probably moved to StateSizedIO.Base
--  and by accident left here. Delete this.
record Interfaceˢ : Set₁ where
  field
    Stateˢ    : Set
    Methodˢ   : Stateˢ → Set
    Resultˢ   : (s : Stateˢ) → (m : Methodˢ s) → Set
    nextˢ     : (s : Stateˢ) → (m : Methodˢ s) → Resultˢ s m → Stateˢ
open Interfaceˢ public
-}

--\StateSizedRObjectRInterface
--@BEGIN@RInterface
record RInterfaceˢ : Set₁ where
  field
    Stateˢ    :  Set
    Methodˢ   :  (s : Stateˢ) → Set
    Resultˢ   :  (s : Stateˢ) → (m : Methodˢ s) → Set
    nextˢ     :  (s : Stateˢ) → (m : Methodˢ s) → (r : Resultˢ s m) → Stateˢ
    RMethodˢ  :  (s : Stateˢ) → Set
    RResultˢ  :  (s : Stateˢ) → (m : RMethodˢ s) → Set
--@END

open RInterfaceˢ public



module _ (I : RInterfaceˢ)(let S = Stateˢ I) (let M = Methodˢ I)
         (let R = Resultˢ I) (let next = nextˢ I)
         (let RM = RMethodˢ I)
         (let RR = RResultˢ I)
          where
  -- A simple object just returns for a method the response
  -- and the object itself
--\StateSizedRObjectRObject
--@BEGIN@RObject
  record RObjectˢ (s : S) : Set where
    coinductive --@HIDE-BEG
    field
--@HIDE-END
      objectMethod  :  (m : M s) → Σ[ r ∈ R s m ] RObjectˢ (next s m r)
      readerMethod  :  (m : RM s) → RR s m
--@END
  open RObjectˢ public




-- Bisimilation for Objectˢ
{-
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
-}
