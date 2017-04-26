

module src.SizedIO.Base where

open import Data.Maybe.Base
open import Data.Sum renaming (inj₁ to left; inj₂ to right; [_,_]′ to either)

open import Function
--open import Level using (_⊔_) renaming (suc to lsuc)
open import Size
open import Data.List
open import src.SizedIO.Object

open import src.NativeIO
open import Data.Product

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

objectInterfToIOInterf : Interface → IOInterface
objectInterfToIOInterf I .Command = I .Method
objectInterfToIOInterf I .Response = I .Result


ioInterfToObjectInterf : IOInterface → Interface
ioInterfToObjectInterf I .Method = I .Command
ioInterfToObjectInterf I .Result = I .Response



module _  {I : IOInterface } (let C = Command I) (let R = Response I) where

  return : ∀{i}{A : Set} (a : A) → IO I i A
  return a .force = return' a

  do : ∀{i}{A : Set} (c : C) (f : R c → IO I i A) → IO I i A
  do c f .force = do' c f

  do1 :  ∀{i} (c : C) → IO I i (R c)
  do1 c = do c return

  infixl 2 _>>=_ _>>='_ _>>_

  mutual
    _>>='_ : ∀{i}{A B : Set}(m : IO' I i A) (k : A → IO I (↑ i) B) → IO' I i B
    do' c f    >>=' k = do' c λ x → f x >>= k
    return' a >>=' k = (k a) .force

    _>>=_ : ∀{i}{A B : Set}(m : IO I i A) (k : A → IO I i B) → IO I i B
    (m >>= k) .force = m .force >>=' k

  _>>_ : ∀{i}{B : Set} (m : IO I i Unit) (k : IO I i B) → IO I i B
  m >> k = m >>= λ _ → k

  {-# NON_TERMINATING #-}
  translateIO : ∀{A : Set}
    →  (translateLocal : (c : C) → NativeIO (R c))
    →  IO I ∞ A
    →  NativeIO A
  translateIO translateLocal m = case (m .force {_}) of
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
  fromIO+ (do' c f) .force = do' c f

  _>>=+'_ : ∀{i}{A B : Set}(m : IO+ I i A) (k : A → IO I i B) → IO' I i B
  do' c f >>=+' k = do' c λ x → f x >>= k

  _>>=+_ : ∀{i}{A B : Set}(m : IO+ I i A) (k : A → IO I i B) → IO I i B
  (m >>=+ k) .force = m >>=+' k

  mutual

    _>>+_ : ∀{i}{A B : Set}(m : IO I i (A ⊎ B)) (k : A → IO I i B) → IO I i B
    (m >>+ k) .force = m .force >>+' k

    _>>+'_ : ∀{j}{A B : Set} (m : IO' I j (A ⊎ B)) (k : A → IO I (↑ j) B) → IO' I j B
    do' c f            >>+' k = do' c λ x → f x >>+ k
    return' (left  a) >>+' k = k a .force
    return' (right b) >>+' k = return' b

   -- loop

  trampoline : ∀{i}{A S : Set} (f : S → IO+ I i (S ⊎ A)) (s : S) → IO I i A
  trampoline f s .force = case (f s) of
    \{ (do' c k) → do' c λ r → k r >>+ trampoline f }

  -- simple infinite loop

  forever : ∀{i}{A B : Set} → IO+ I i A → IO I i B
  forever (do' c f) .force = do' c λ r → f r >>= λ _ → forever (do' c f)

  whenJust : ∀{i}{A : Set} → Maybe A → (A → IO I i (Unit )) → IO I i Unit
  whenJust nothing  k = return _
  whenJust (just a) k = k a


mutual
  mapIO : ∀ {i} → {I : IOInterface} → {A B : Set} → (A → B) → IO I i  A  → IO I i B
  mapIO f p .force = mapIO' f (p .force)

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



module _  {I : IOInterface }
          (let C = Command I)
          (let R = Response I)
           where
  mutual
    fmap : (i : Size) → {A B : Set} → (f : A → B)
            → IO I i A
            → IO I i B
    fmap i {A} {B} f p .force {j} = fmap' j {A} {B} f (p .force {j})


    fmap' : (i : Size) → {A B : Set} → (f : A → B )
            → IO' I i A
            → IO' I i B
    fmap' i {A} {B} f (do' c f₁) = do' c (λ r → fmap i {A} {B} f (f₁ r))
    fmap' i {A} {B} f (return' a) = return' (f a)


module _ (I : IOInterface )
         (let C = I .Command)
         (let R = I .Response)
           where

    data IOind (A : Set) : Set where

      do''     : (c : C) (f : (r : R c) → IOind A) → IOind A
      return'' : (a : A) → IOind A

_>>''_ : {I : IOInterface}(let C = I .Command)(let R = I .Response)
         {A B : Set} (p : IOind I A) (q : A → IOind I B) → IOind I B
do'' c f >>'' q = do'' c (λ r →  f r >>'' q)
return'' a >>'' q = q a

module _ {I : Interface }
         (let M = I .Method)
         (let R = I .Result)
           where


  translate : ∀{A : Set}
               → Object I
               → IOind (objectInterfToIOInterf I) A
               →  A × Object I
  translate {A} obj (do'' c p) = obj .objectMethod c ▹ λ {(x , o')
                                      → translate {A} o' (p x)  }
  translate {A} obj (return'' a) = a , obj
