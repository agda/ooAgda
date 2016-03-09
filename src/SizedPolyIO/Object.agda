module SizedPolyIO.Object where

open import Data.Product

open import Level using (_⊔_) renaming (suc to lsuc)

record Interface μ ρ : Set (lsuc (μ ⊔ ρ)) where
  field
    Method  : Set μ
    Result  : (m : Method) → Set ρ
open Interface public

-- A simple object just returns for a method the response
-- and the object itself
record Object {μ ρ} (i : Interface μ ρ) : Set (μ ⊔ ρ) where
  coinductive
  field
    objectMethod : (m : Method i) → Result i m × Object i

open Object public
