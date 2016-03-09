module UnSizedIO.IOObject where

open import Data.Product

open import UnSizedIO.Base
open import UnSizedIO.Object

-- An IO object is like a simple object,
-- but the method returns IO applied to the result type of a simple object
-- which means the method returns an IO program which when terminating
-- returns the result of the simple object


module _  (ioi  : IOInterface)  (let C  = Command ioi)  (let R   = Response ioi)
          (oi   : Interface)   (let M  = Method oi)    (let Rt  = Result oi)
  where

  record IOObject : Set where
    coinductive
    field
      method : (m : M) → IO ioi (Rt m × IOObject)

open IOObject public
