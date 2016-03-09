module SizedIO.coIOIOObject where

open import Data.Unit.Base
open import Data.Product
open import Data.String.Base

open import Size

open import SizedIO.Object

open import SizedIO.Base
open import SizedIO.Console
open import SizedIO.coIOIO
-- open import SizedIO.IOObject


record IOObject' (i : Size) (iface : Interface)(C : Set)(R : C → Set) : Set
  where
  coinductive
  field
    method : ∀{j : Size< i} (m : Method iface) →
             IO j C R (Response iface m × IOObject' j iface C R)
open IOObject' public



-- An IO object is like a simple object,
-- but the method returns IO applied to the result type of a simple object
-- which means the method returns an IO program which when terminating
-- returns the result of the simple object
record coIO²Object (i : Size) (iface : Interface)
                (Cin : Set)(Rin : Cin → Set)
                (Cext : Set)(Rext : Cext → Set)     : Set
  where
  coinductive
  field
    method' : ∀{j : Size< i} (m : Method iface) →
             coIO²∞  ∞  Cin Rin Cext Rext
                     (Response iface m × coIO²Object j iface Cin Rin Cext Rext)
open coIO²Object public


selfrefIOObject : (i : Size) (iface : Interface)
                  (Cext : Set) (Rext : Cext → Set) → Set
selfrefIOObject i iface Cext Rext = coIO²Object i iface (Method iface)
                                    (Response iface) Cext Rext

mutual
  compileSelfRef : (i : Size) (iface : Interface)
                   (Cext : Set) (Rext : Cext → Set)
                   (obj : selfrefIOObject i iface Cext Rext) →
                   IOObject' i iface Cext Rext
  IO.force (method (compileSelfRef i iface Cext Rext obj) {i'} m) {j} =
           compileSelfRefaux  i' j iface Cext Rext (Response iface m) (coIO²∞.force (method' obj {i'} m) j)

  compileSelfRefaux :
    (i : Size) (j : Size< i)
    (iface : Interface) (let M = Method iface) (let R = Response iface)
    (Cext : Set) (Rext : Cext → Set)
    (A : Set)
    (coObj : coIO² ∞ j M R Cext Rext (A × coIO²Object i iface M R Cext Rext))
    → IO' j Cext Rext (A × IOObject' i iface Cext Rext)
  compileSelfRefaux i j iface Cext Rext A (coIO².return (r , obj)) = return' (r , compileSelfRef i iface Cext Rext obj)
  compileSelfRefaux i j iface Cext Rext A (dof i' m f) = {! >>=!}
  compileSelfRefaux i j iface Cext Rext A (do∞ c f) =
         do' c (λ r → compileSelfRefaux'' i j iface Cext Rext A (f r))



  compileSelfRefaux'' : (i : Size) (j : Size< i)
    (iface : Interface) (let M = Method iface) (let R = Response iface)
    (Cext : Set) (Rext : Cext → Set)
    (A : Set)
    (coObj : coIO²∞ j M R Cext Rext (A × coIO²Object i iface M R Cext Rext))
      → IO j Cext Rext (A × IOObject' i iface Cext Rext)
  IO.force (compileSelfRefaux'' i j iface Cext Rext A coObj) {j''} = compileSelfRefaux i j'' iface Cext Rext A (coIO²∞.force coObj j'')


--  compileSelfRefaux'' i' j iface Cext Rext A coObj
--           = compileSelfRefaux' i' j iface Cext Rext A (coIO²∞.force coObj {!!})

{-
  compileSelfRefaux' :
    (i' : Size) (j : Size< i')
    (iface : Interface) (let M = Methods iface) (let R = Responses iface)
    (Cext : Set) (Rext : Cext → Set)
    (A : Set)
    (coObj : coIO² ∞ j M R Cext Rext (A × coIO²Object i' iface M R Cext Rext))
    → IO j Cext Rext (A × IOObject' i' iface Cext Rext)
  IO.force (compileSelfRefaux' i' j iface Cext Rext A coObj) = compileSelfRefaux i' j iface Cext Rext A coObj
-}
{-
123;456hallo789
123;456hallo789
123;789hallo456
123;789hallo456
123;789456
123;789456
123;456789
123;456789
123;456789
123;456789

C-x r k    -- kill rectangle
C-x r y    -- yank rectangle
C-x r t    -- text rectangle
-}

{-
M-x abbrev-mode

C-x ail

crosss
→

\
-}


-- method' obj {j'} m

{-
  compileSelfRefaux :  (j' : Size) (iface : Interface)
                       (Cext : Set) (Rext : Cext → Set)
                       (m : Methods iface)
                       ( p : coIO²∞ ∞ (Methods iface)
                                      (Responses iface) Cext Rext
                                      (Responses iface m ×
                                       coIO²Object j' iface (Methods iface)
                                       (Responses iface) Cext Rext))
                       → IO' j' Cext Rext
                         (Responses iface m ×
                          IOObject' j iface Cext Rext)IO' j' Cext Rext
                          (Responses iface m × IOObject' j iface Cext Rext)

  -}
