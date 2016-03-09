module StateSizedIO.IOObject where

open import Data.Product

open import Size

open import SizedIO.Base
open import StateSizedIO.Object

-- An IO object is like a simple object,
-- but the method returns IO applied to the result type of a simple object
-- which means the method returns an IO program which when terminating
-- returns the result of the simple object

module _  (ioi  : IOInterface)  (let C = Command ioi)  (let R = Response ioi)
          (oi   : Interfaceˢ)    (let S = Stateˢ oi)     (let M  = Methodˢ oi)
                                (let Rt  = Resultˢ oi) (let next = nextˢ oi)

  where

  record IOObject (i : Size) (s : S) : Set where
    coinductive
    field
      method : ∀{j : Size< i} (m : M s) → IO ioi ∞ (Σ[ r ∈ Rt s m ] IOObject j (next s m r) )

open IOObject public
