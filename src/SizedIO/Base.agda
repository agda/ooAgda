{-# OPTIONS --copatterns #-}

module SizedIO.Base where

open import Data.Maybe.Base
open import Data.Sum renaming (inj₁ to left; inj₂ to right; [_,_]′ to either)
open import Data.List

open import Function
--open import Level using (_⊔_) renaming (suc to lsuc)
open import Size renaming (ω to ∞ )

open import NativeIO

record IOInterface  : Set₁ where
  field
    Command   : Set
    Response  : (m : Command) → Set
open IOInterface public

module _ (I : IOInterface ) (let C = Command I) (let R = Response I) where

  mutual
    record IO (i : Size)  (A : Set) : Set where
      coinductive
      constructor delay
      field
        force : {j : Size< i} → IO' j A

    data IO' (i : Size)  (A : Set) : Set where
      do'     : (c : C) (f : R c → IO i A) → IO' i A
      return' : (a : A) → IO' i A

  data IO+ (i : Size)  (A : Set) : Set where
    do' : (c : C) (f : R c → IO i A) → IO+ i A

open IO public

module _  {I : IOInterface } (let C = Command I) (let R = Response I) where

  return : ∀{i}{A : Set} (a : A) → IO I i A
  force (return a) = return' a

  exec : ∀{i}{A : Set} (c : C) (f : R c → IO I i A) → IO I i A
  force (exec c f) = do' c f

  exec1 :  ∀{i} (c : C) → IO I i (R c)
  exec1 c = exec c return

  infixl 2 _>>=_ _>>='_ _>>_

  mutual
    _>>='_ : ∀{i}{A B : Set}(m : IO' I i A) (k : A → IO I (↑ i) B) → IO' I i B
    do' c f    >>=' k = do' c λ x → f x >>= k
    return' a >>=' k = force (k a)

    _>>=_ : ∀{i}{A B : Set}(m : IO I i A) (k : A → IO I i B) → IO I i B
    force (m >>= k) = force m >>=' k

  _>>_ : ∀{i}{B : Set} (m : IO I i Unit) (k : IO I i B) → IO I i B
  m >> k = m >>= λ _ → k

  {-# NON_TERMINATING #-}
  translateIO : ∀{A : Set}
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

  fromIO+' : ∀{i}{A : Set} → IO+ I i A → IO' I i A
  fromIO+' (do' c f) = do' c f

  fromIO+ : ∀{i}{A : Set} → IO+ I i A → IO I i A
  force (fromIO+ (do' c f)) = do' c f

  _>>=+'_ : ∀{i}{A B : Set}(m : IO+ I i A) (k : A → IO I i B) → IO' I i B
  do' c f >>=+' k = do' c λ x → f x >>= k

  _>>=+_ : ∀{i}{A B : Set}(m : IO+ I i A) (k : A → IO I i B) → IO I i B
  force (m >>=+ k) = m >>=+' k

  mutual

    _>>+_ : ∀{i}{A B : Set}(m : IO I i (A ⊎ B)) (k : A → IO I i B) → IO I i B
    force (m >>+ k) = force m >>+' k

    _>>+'_ : ∀{j}{A B : Set} (m : IO' I j (A ⊎ B)) (k : A → IO I (↑ j) B) → IO' I j B
    do' c f            >>+' k = do' c λ x → f x >>+ k
    return' (left  a) >>+' k = force (k a)
    return' (right b) >>+' k = return' b

   -- loop

  trampoline : ∀{i}{A S : Set} (f : S → IO+ I i (S ⊎ A)) (s : S) → IO I i A
  force (trampoline f s) = case (f s) of
    \{ (do' c k) → do' c λ r → k r >>+ trampoline f }

  -- simple infinite loop

  forever : ∀{i}{A B : Set} → IO+ I i A → IO I i B
  force (forever (do' c f)) = do' c λ r → f r >>= λ _ → forever (do' c f)

  whenJust : ∀{i}{A : Set} → Maybe A → (A → IO I i (Unit )) → IO I i Unit
  whenJust nothing  k = return _
  whenJust (just a) k = k a


mutual
  mapIO : ∀ {i} → {I : IOInterface} → {A B : Set} → (A → B) → IO I i  A  → IO I i B
  force (mapIO f p) = mapIO' f (force p)

  mapIO' : ∀ {i} → {I : IOInterface} → {A B : Set} → (A → B) → IO' I i  A  → IO' I i B
  mapIO' f (do' c g) = do' c (λ r → mapIO f (g r))
  mapIO' f (return' a) = return' (f a)


sequenceIO : {i : IOInterface} →  List  (IO  i ∞ Unit) → IO i ∞ Unit
sequenceIO [] .force = return' unit
sequenceIO (p ∷ l) = p >>= (λ _ → sequenceIO l)


Return : {i : Size} → {int : IOInterface} →  {A : Set} → A → IO int i A
Return a .force = return' a

Do : {i : Size} → {int : IOInterface} → (c : int .Command)
                → IO int i (int .Response c)
Do c .force = do' c Return
