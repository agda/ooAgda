{-# OPTIONS --postfix-projections #-}

module UnSizedIO.Base where

open import Data.Maybe.Base
open import Data.Sum renaming (inj₁ to left; inj₂ to right; [_,_]′ to either)
open import Function

open import NativeIO

record IOInterface : Set₁ where
  field
    Command   : Set
    Response : (m : Command) → Set
open IOInterface public

module _ (I : IOInterface) (let C = Command I) (let R = Response I) (A : Set)
  where

  mutual
    record IO : Set where
      coinductive
      constructor delay
      field
        force : IO'

    data IO' : Set where
      exec'      : (c : C) (f : R c → IO) → IO'
      return' : (a : A) → IO'

open IO public

module _ {I : IOInterface} (let C = Command I) (let R = Response I)
      where
  return : ∀{A} (a : A) → IO I A
  return a .force = return' a

  exec : ∀{A} (c : C) (f : R c → IO I A) → IO I A
  exec c f .force = exec' c f

  exec1 :  (c : C) → IO I (R c)
  exec1 c = exec c return

  infixl 2 _>>=_ _>>='_ _>>_

  mutual
    _>>='_ : ∀{A B} (m : IO' I A) (k : A → IO I B) → IO' I B
    exec' c f    >>=' k = exec' c λ x → f x >>= k
    return' a >>=' k = force (k a)

    _>>=_ : ∀{A B} (m : IO I A) (k : A → IO I B) → IO I B
    force (m >>= k) = force m >>=' k

  _>>_ : ∀{B} (m : IO I Unit) (k : IO I B) → IO I B
  m >> k = m >>= λ _ → k


module _ {I : IOInterface} (let C = Command I) (let R = Response I)
      where
  {-# NON_TERMINATING #-}
  translateIO : ∀ {A}
    →  (translateLocal : (c : C) → NativeIO (R c))
    →  IO I A
    →  NativeIO A
  translateIO translateLocal m = case (m .force) of
    λ{ (exec' c f)    → (translateLocal c) native>>= λ r →
         translateIO translateLocal (f r)
     ; (return' a) → nativeReturn a
     }

-- Recursion

-- trampoline provides a generic form of loop (generalizing while/repeat).
-- Starting at state s : S, step function f is iterated until it returns
-- a result in A.

module _ (I : IOInterface)(let C = Command I) (let R = Response I)
      where
  data IO+ (A : Set) : Set where
      exec' : (c : C) (f : R c → IO I A) → IO+ A

module _ {I : IOInterface}(let C = Command I) (let R = Response I)
      where
  fromIO+' : ∀{A} → IO+ I A → IO' I A
  fromIO+' (exec' c f) = exec' c f

  fromIO+ : ∀{A} → IO+ I A → IO I A
  fromIO+ (exec' c f) .force = exec' c f

  _>>=+'_ : ∀{A B} (m : IO+ I A) (k : A → IO I B) → IO' I B
  exec' c f >>=+' k = exec' c λ x → f x >>= k

  _>>=+_ : ∀{A B} (m : IO+ I A) (k : A → IO I B) → IO I B
  force (m >>=+ k) = m >>=+' k

  mutual

    _>>+_ : ∀{A B} (m : IO I (A ⊎ B)) (k : A → IO I B) → IO I B
    force (m >>+ k) = force m >>+' k

    _>>+'_ : ∀{A B} (m : IO' I (A ⊎ B)) (k : A → IO I B) → IO' I B
    exec' c f            >>+' k = exec' c λ x → f x >>+ k
    return' (left  a) >>+' k = force (k a)
    return' (right b) >>+' k = return' b

   -- loop

  {-# TERMINATING #-}
  trampoline : ∀{A S} (f : S → IO+ I (S ⊎ A)) (s : S) → IO I A
  force (trampoline f s) = case (f s) of
    \{ (exec' c k) → exec' c λ r → k r >>+ trampoline f }

  -- simple infinite loop

  {-# TERMINATING #-}
  forever : ∀{A B} → IO+ I A → IO I B
  force (forever (exec' c f)) = exec' c λ r → f r >>= λ _ → forever (exec' c f)

  whenJust : {A : Set} → Maybe A → (A → IO I Unit) → IO I Unit
  whenJust nothing  k = return _
  whenJust (just a) k = k a

module _ (I : IOInterface )
         (let C = I .Command)
         (let R = I .Response)
           where

    data IOind (A : Set) : Set where

      exec''     : (c : C) (f : (r : R c) → IOind A) → IOind A
      return'' : (a : A) → IOind A



main : NativeIO Unit
main = nativePutStrLn "Hello, world!"
