--@PREFIX@StateSizedRObject

module src.StateSizedIO.RObject where

open import Data.Product
open import src.StateSizedIO.Base public

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
