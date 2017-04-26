--@PREFIX@StateSizedBase
module src.StateSizedIO.Base where

open import Size
open import src.SizedIO.Base

open import Data.Product

record IOInterfaceˢ  : Set₁ where
  field
    IOStateˢ   :  Set
    Commandˢ   :  IOStateˢ → Set
    Responseˢ  :  (s : IOStateˢ) → (m : Commandˢ s) → Set
    IOnextˢ    :  (s : IOStateˢ) → (m : Commandˢ s) → (Responseˢ s m) → IOStateˢ
open IOInterfaceˢ public

--\StateSizedBasestateinterface
--@BEGIN@stateinterface
record Interfaceˢ : Set₁ where --@HIDE-BEG
  field
--@HIDE-END
    Stateˢ   :  Set
    Methodˢ  :  Stateˢ → Set
    Resultˢ  :  (s : Stateˢ) → (m : Methodˢ s) → Set
    nextˢ    :  (s : Stateˢ) → (m : Methodˢ s) → (Resultˢ s m) → Stateˢ
open Interfaceˢ public
--@END

module _  (ioi  : IOInterface)  (let C  = Command ioi)  (let R   = Response ioi)
          (oi   : Interfaceˢ)   (let S = Stateˢ oi) (let M  = Methodˢ oi)    (let Rt  = Resultˢ oi)
                                (let n = nextˢ oi)
  where

  record IOObjectˢ (i : Size) (s : S) : Set where
    coinductive
    field
      method : ∀{j : Size< i} (m : M s) → IO ioi ∞ ( Σ[ r ∈ Rt s m ] IOObjectˢ j (n s m r))

open IOObjectˢ public



module _ (I : IOInterfaceˢ )
         (let S = IOStateˢ I) (let C = Commandˢ I)
         (let R = Responseˢ I) (let n = IOnextˢ I)
           where

  mutual
    record IOˢ (i : Size)  (A : S → Set) (s : S) : Set where
      coinductive
      -- constructor delay
      field
        forceˢ : {j : Size< i} → IOˢ' j A s

    data IOˢ' (i : Size)  (A : S → Set) (s : S) : Set where
      doˢ'      :  (c : C s) (f : (r : R s c) → IOˢ i A (n s c r)) → IOˢ' i A s
      returnˢ'  :  (a : A s) → IOˢ' i A s

    data IOˢ+ (i : Size)  (A : S → Set) (s : S) : Set where
      doˢ' : (c : C s)  (f : (r : R s c) → IOˢ i A (n s c r)) → IOˢ+ i A s

open IOˢ public

delayˢ : {i : Size}{I : IOInterfaceˢ}{A : IOStateˢ I → Set}{s : IOStateˢ I} → IOˢ' I i A s → IOˢ I (↑ i) A s
delayˢ p .forceˢ = p



module _  {I : IOInterfaceˢ }
          (let S = IOStateˢ I) (let C = Commandˢ I)
          (let R = Responseˢ I) (let n = IOnextˢ I)
           where
  returnˢ : ∀{i}{A : S → Set} (s : S) (a : A s) → IOˢ I i A s
  returnˢ s a .forceˢ = returnˢ' a

  -- 2017-04-05: Argument s is hidden now.
  doˢ : ∀{i}{A : S → Set} {s : S} (c : C s)
           (f : (r : R s c) → IOˢ I i A (n s c r))
           → IOˢ I i A s
  doˢ c f .forceˢ = doˢ' c f


  mutual
    fmapˢ : (i : Size) → {A B : S → Set} → (f : (s : S) → A s → B s)
            → (s : S)
            → IOˢ I i A s
            → IOˢ I i B s
    fmapˢ i {A} {B} f s p .forceˢ {j} = fmapˢ' j {A} {B} f s (p .forceˢ {j})


    fmapˢ' : (i : Size) → {A B : S → Set} → (f : (s : S) → A s → B s)
            → (s : S)
            → IOˢ' I i A s
            → IOˢ' I i B s
    fmapˢ' i {A} {B} f s (doˢ' c f₁) = doˢ' c (λ r → fmapˢ i {A} {B} f (IOnextˢ I s c r)  (f₁ r))
    fmapˢ' i {A} {B} f s (returnˢ' a) = returnˢ' (f s a)
