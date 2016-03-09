module SizedIO.IOObject where

open import Data.Product

open import Size

open import SizedIO.Base
open import SizedIO.Object

-- An IO object is like a simple object,
-- but the method returns IO applied to the result type of a simple object
-- which means the method returns an IO program which when terminating
-- returns the result of the simple object

module _  (ioi  : IOInterface)  (let C  = Command ioi)  (let R   = Response ioi)
          (oi   : Interface)   (let M  = Method oi)    (let Rt  = Result oi)
  where

  record IOObject (i : Size) : Set where
    coinductive
    field
      method : ∀{j : Size< i} (m : M) → IO ioi ∞ (Rt m × IOObject j)

open IOObject public
