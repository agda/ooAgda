{-# OPTIONS --copatterns #-}

module SizedPolyIO.Base where

open import Data.Maybe.Base
open import Data.Sum renaming (inj₁ to left; inj₂ to right; [_,_]′ to either)

open import Function
open import Level using (_⊔_) renaming (suc to lsuc)
open import Size

open import NativePolyIO

record IOInterface γ ρ : Set (lsuc (γ ⊔ ρ)) where
  field
    Command   : Set γ
    Response  : (m : Command) → Set ρ
open IOInterface public

module _ {γ ρ} (I : IOInterface γ ρ) (let C = Command I) (let R = Response I) where

  mutual
    record IO (i : Size) {α} (A : Set α) : Set (α ⊔ γ ⊔ ρ) where
      coinductive
      constructor delay
      field
        force : {j : Size< i} → IO' j A

    data IO' (i : Size) {α} (A : Set α) : Set (α ⊔ γ ⊔ ρ) where
      do'      : (c : C) (f : R c → IO i A) → IO' i A
      return' : (a : A) → IO' i A

    data IO+ (i : Size) {α} (A : Set α) : Set (α ⊔ ρ ⊔ γ) where
      do' : (c : C) (f : R c → IO i A) → IO+ i A

open IO public

module _ {γ ρ} {I : IOInterface γ ρ} (let C = Command I) (let R = Response I) where

  return : ∀{i α}{A : Set α} (a : A) → IO I i A
  force (return a) = return' a

  do : ∀{i α}{A : Set α} (c : C) (f : R c → IO I i A) → IO I i A
  force (do c f) = do' c f

  do1 :  ∀{i} (c : C) → IO I i (R c)
  do1 c = do c return

  infixl 2 _>>=_ _>>='_ _>>_

  mutual
    _>>='_ : ∀{i α}{A B : Set α} (m : IO' I i A) (k : A → IO I (↑ i) B) → IO' I i B
    do' c f    >>=' k = do' c λ x → f x >>= k
    return' a >>=' k = force (k a)

    _>>=_ : ∀{i α}{A B : Set α} (m : IO I i A) (k : A → IO I i B) → IO I i B
    force (m >>= k) = force m >>=' k

  _>>_ : ∀{i α}{B : Set α} (m : IO I i Unit) (k : IO I i B) → IO I i B
  m >> k = m >>= λ _ → k

  {-# NON_TERMINATING #-}
  translateIO : ∀{α}{A : Set α}
    →  (translateLocal : (c : C) → NativeIO (R c))
    →  IO I ∞ A
    →  NativeIO A
  translateIO translateLocal m = case (force m {_}) of
    λ{ (do' c f)    → (translateLocal c) native>>= λ r →
         translateIO translateLocal (f r)
     ; (return' a) → nativeReturn a
     }

  -- Recursion

  -- trampoline provides a generic form of loop (generalizing while/repeat).
  -- Starting at state s : S, step function f is iterated until it returns
  -- a result in A.

  fromIO+' : ∀{i α}{A : Set α} → IO+ I i A → IO' I i A
  fromIO+' (do' c f) = do' c f

  fromIO+ : ∀{i α}{A : Set α} → IO+ I i A → IO I i A
  force (fromIO+ (do' c f)) = do' c f

  _>>=+'_ : ∀{i α}{A B : Set α} (m : IO+ I i A) (k : A → IO I i B) → IO' I i B
  do' c f >>=+' k = do' c λ x → f x >>= k

  _>>=+_ : ∀{i α}{A B : Set α} (m : IO+ I i A) (k : A → IO I i B) → IO I i B
  force (m >>=+ k) = m >>=+' k

  mutual

    _>>+_ : ∀{i α}{A B : Set α} (m : IO I i (A ⊎ B)) (k : A → IO I i B) → IO I i B
    force (m >>+ k) = force m >>+' k

    _>>+'_ : ∀{j α}{A B : Set α} (m : IO' I j (A ⊎ B)) (k : A → IO I (↑ j) B) → IO' I j B
    do' c f            >>+' k = do' c λ x → f x >>+ k
    return' (left  a) >>+' k = force (k a)
    return' (right b) >>+' k = return' b

   -- loop

  trampoline : ∀{i α}{A S : Set α} (f : S → IO+ I i (S ⊎ A)) (s : S) → IO I i A
  force (trampoline f s) = case (f s) of
    \{ (do' c k) → do' c λ r → k r >>+ trampoline f }

  -- simple infinite loop

  forever : ∀{i α}{A B : Set α} → IO+ I i A → IO I i B
  force (forever (do' c f)) = do' c λ r → f r >>= λ _ → forever (do' c f)

  whenJust : ∀{i α}{A : Set α} → Maybe A → (A → IO I i (Unit {α})) → IO I i Unit
  whenJust nothing  k = return _
  whenJust (just a) k = k a
