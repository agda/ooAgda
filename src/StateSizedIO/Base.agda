
module StateSizedIO.Base where

open import Size
open import SizedIO.Base

open import Data.Product

record IOInterfaceˢ  : Set₁ where
  field
    IOStateˢ   : Set
    Commandˢ   : IOStateˢ → Set
    Responseˢ  : (s : IOStateˢ) → (m : Commandˢ s) → Set
    IOnextˢ      : (s : IOStateˢ) → (m : Commandˢ s) → (Responseˢ s m) → IOStateˢ
open IOInterfaceˢ public


record Interfaceˢ : Set₁ where
  field
    Stateˢ     : Set
    Methodˢ   : Stateˢ → Set
    Resultˢ  : (s : Stateˢ) → (m : Methodˢ s) → Set
    nextˢ      : (s : Stateˢ) → (m : Methodˢ s) → (Resultˢ s m) → Stateˢ
open Interfaceˢ public


module _  (ioi  : IOInterface)  (let C  = Command ioi)  (let R   = Response ioi)
          (oi   : Interfaceˢ)   (let S = Stateˢ oi) (let M  = Methodˢ oi)    (let Rt  = Resultˢ oi)
                                (let n = nextˢ oi)
  where

  record IOObjectˢ (i : Size) (s : Stateˢ) : Set where
    coinductive
    field
      method : ∀{j : Size< i} (m : M s) → IO ioi ∞ ( Σ[ r ∈ Rt s m ] IOObjectˢ j (n s m r))

open IOObjectˢ public



module _ (I : IOInterfaceˢ )
         (let S = IOStateˢ I) (let C = Commandˢ I)
         (let R = Responseˢ I) (let n = nextˢ I)
           where

  mutual
    record IOˢ (i : Size)  (A : S → Set) (s : S) : Set where
      coinductive
      constructor delay
      field
        forceˢ : {j : Size< i} → IOˢ' j A s

    data IOˢ' (i : Size)  (A : S → Set) (s : S) : Set where
      doˢ'      : (c : C s) (f : (r : R s c) → IOˢ i A (n s c r)) → IOˢ' i A s
      returnˢ' : (a : A s) → IOˢ' i A s

    data IOˢ+ (i : Size)  (A : S → Set) (s : S) : Set where
      do' : (c : C s)  (f : (r : R s c) → IOˢ i A (n s c r)) → IOˢ+ i A s

open IOˢ public

module _  {I : IOInterfaceˢ }
          (let S = Stateˢ I) (let C = Commandˢ I)
          (let R = Responseˢ I) (let n = nextˢ I)
           where
  returnˢ : ∀{i}{A : S → Set} (s : S) (a : A s) → IOˢ I i A s
  forceˢ (returnˢ s a) = returnˢ' a

  doˢ : ∀{i}{A : S → Set} (s : S) (c : C s)
           (f : (r : R s c) → IOˢ I i A (n s c r))
           → IOˢ I i A s
  forceˢ (doˢ s c f) = doˢ' c f
