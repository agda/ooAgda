module examplesPaperJFP.BasicIO where

open import Data.Maybe hiding ( _>>=_ )
open import Data.Sum renaming (inj₁ to left; inj₂ to right; [_,_]′ to either)
open import Function

open import examplesPaperJFP.NativeIOSafe
open import examplesPaperJFP.triangleRightOperator

module _ where  -- for indentation
  record IOInterface : Set₁ where
    field  Command   :  Set
           Response  :  (c : Command) → Set


open IOInterface public

module _ {C : Set} {R : C → Set} (let
  I = record { Command = C; Response = R }
    ) where
module Postulated {I : IOInterface} (let C = Command I) (let R = Response I) where

  postulate
    IO                :  (I : IOInterface) (A : Set) → Set
    exec               :  ∀{A}    (c  :  C)       (f  :  R c → IO I A)  → IO I A
    return            :  ∀{A}    (a  :  A)                             → IO I A
    _>>=_             :  ∀{A B}  (m  :  IO I A)  (k  :  A → IO I B)    → IO I B

mutual
  record IO I A : Set where
    coinductive
    constructor delay
    field force : IO′ I A

  data IO′ I A : Set where
    exec′      :  (c : Command I) (f : Response I c → IO I A)  → IO′ I A
    return′  :  (a : A)                                      → IO′ I A

open IO public

delay′ : ∀{I A} → IO′ I A → IO I A
force (delay′ x) = x

module _ {I : IOInterface} (let C = Command I) (let R = Response I) where
-- module _ {I : IOInterface} (let record { Command = C; Response = R } = I) where
-- module _ {I : IOInterface} (let ioInterface C R = I) where
  exec                :  ∀{A} (c : C) (f : R c → IO I A) → IO I A
  force (exec c f)    =  exec′ c f

  return            :  ∀{A} (a : A) → IO I A
  force (return a)  =  return′ a

  infixl 2 _>>=_
  _>>=_             :  ∀{A B} (m : IO I A) (k : A → IO I B) → IO I B
  force (m >>= k) with force m
  ... | exec′ c f     =  exec′ c λ x → f x >>= k
  ... | return′ a   =  force (k a)

module _ {I : IOInterface} (let C = Command I) (let R = Response I)
      where




  {-# NON_TERMINATING #-}
  translateIO : ∀ {A} (tr : (c : C) → NativeIO (R c)) → IO I A → NativeIO A
  translateIO tr m = force m ▹ λ
     {  (exec′ c f)    →  (tr c) native>>= λ r → translateIO tr (f r)
     ;  (return′ a)  →  nativeReturn a
     }

-- Recursion

-- trampoline provides a generic form of loop (generalizing while/repeat).
-- Starting at state s : S, step function f is iterated until it returns
-- a result in A.

module _ (I : IOInterface)(let C = Command I) (let R = Response I)
      where
  data IO+ (A : Set) : Set where
      exec′ : (c : C) (f : R c → IO I A) → IO+ A

module _ {I : IOInterface}(let C = Command I) (let R = Response I)
      where
  fromIO+′ : ∀{A} → IO+ I A → IO′ I A
  fromIO+′ (exec′ c f) = exec′ c f

  fromIO+ : ∀{A} → IO+ I A → IO I A
  force (fromIO+ (exec′ c f)) = exec′ c f

  _>>=+′_ : ∀{A B} (m : IO+ I A) (k : A → IO I B) → IO′ I B
  exec′ c f >>=+′ k = exec′ c λ x → f x >>= k

  _>>=+_ : ∀{A B} (m : IO+ I A) (k : A → IO I B) → IO I B
  force (m >>=+ k) = m >>=+′ k

  mutual

    _>>+_ : ∀{A B} (m : IO I (A ⊎ B)) (k : A → IO I B) → IO I B
    force (m >>+ k) = force m >>+′ k

    _>>+′_ : ∀{A B} (m : IO′ I (A ⊎ B)) (k : A → IO I B) → IO′ I B
    exec′ c f            >>+′ k = exec′ c λ x → f x >>+ k
    return′ (left  a)  >>+′ k = force (k a)
    return′ (right b)  >>+′ k = return′ b

   -- loop

  {-# TERMINATING #-}

  trampoline : ∀{A S} (f : S → IO+ I (S ⊎ A)) (s : S) → IO I A
  force (trampoline f s) = case (f s) of
    \ { (exec′ c k) → exec′ c λ r → k r >>+ trampoline f }

  -- simple infinite loop

  {-# TERMINATING #-}
  forever : ∀{A B} → IO+ I A → IO I B
  force (forever (exec′ c f)) = exec′ c λ r → f r >>= λ _ → forever (exec′ c f)

  whenJust : {A : Set} → Maybe A → (A → IO I Unit) → IO I Unit
  whenJust nothing  k = return _
  whenJust (just a) k = k a


main : NativeIO Unit
main = nativePutStrLn "Hello, world!"
