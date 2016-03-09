module SizedPolyIO.IOObject where

open import Data.Product

open import Level using (_⊔_) renaming (suc to lsuc)
open import Size

open import SizedPolyIO.Base
open import SizedPolyIO.Object

-- An IO object is like a simple object,
-- but the method returns IO applied to the result type of a simple object
-- which means the method returns an IO program which when terminating
-- returns the result of the simple object


module _  {γ ρ}  (ioi  : IOInterface γ ρ)  (let C  = Command ioi)  (let R   = Response ioi)
          {μ σ}  (oi   : Interface μ σ)   (let M  = Method oi)    (let Rt  = Result oi)
  where

  record IOObject (i : Size) : Set (ρ ⊔ γ ⊔ μ ⊔ σ) where
    coinductive
    field
      method : ∀{j : Size< i} (m : M) → IO ioi ∞ (Rt m × IOObject j)

open IOObject public
