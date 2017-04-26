--@PREFIX@writingOOsUsingIOReaderMethods
{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --allow-unsolved-metas #-}


module src.StateSizedIO.writingOOsUsingIOReaderMethods where


open import src.StateSizedIO.RObject
open import src.StateSizedIO.Object
open import src.StateSizedIO.Base
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Bool
open import Function
open import Data.Unit
open import Data.String
open import src.Unit
open import Data.Bool.Base
open import Relation.Binary.PropositionalEquality
open import src.SizedIO.Console
open import Size
open import src.SizedIO.Base
open import Data.Sum
open import Data.Empty


-- ### new imports
--
open import src.StateSizedIO.cellStateDependent using (CellInterfaceˢ; empty; cellPempty')
open import src.NativeIO








objectInterfToIOInterfˢ : RInterfaceˢ → IOInterfaceˢ
objectInterfToIOInterfˢ I .IOStateˢ = I .Stateˢ
objectInterfToIOInterfˢ I .Commandˢ s = I .Methodˢ s ⊎ I .RMethodˢ s
objectInterfToIOInterfˢ I .Responseˢ s (inj₁ c) = I .Resultˢ s c
objectInterfToIOInterfˢ I .Responseˢ s (inj₂ c) = I .RResultˢ s c -- I .Resultˢ
objectInterfToIOInterfˢ I .IOnextˢ s (inj₁ c) r = I .nextˢ s c r
objectInterfToIOInterfˢ I .IOnextˢ s (inj₂ c) r = s -- I .nextˢ


ioInterfToObjectInterfˢ : IOInterfaceˢ → RInterfaceˢ
ioInterfToObjectInterfˢ I .Stateˢ = I .IOStateˢ
ioInterfToObjectInterfˢ I .Methodˢ = I .Commandˢ
ioInterfToObjectInterfˢ I .Resultˢ = I .Responseˢ --
ioInterfToObjectInterfˢ I .nextˢ = I .IOnextˢ
ioInterfToObjectInterfˢ I .RMethodˢ s = ⊥
ioInterfToObjectInterfˢ I .RResultˢ s ()


data DecSets : Set where
  fin : ℕ → DecSets

TDecSets : DecSets → Set
TDecSets (fin n) = Fin n

toDecSets : ∀{n} → (x : Fin n) → DecSets
toDecSets x = fin (toℕ x)

_==fin_ : {n : ℕ} → Fin n → Fin n → Bool
_==fin_ {zero} () t
_==fin_ {suc _} zero zero = true
_==fin_ {suc _} zero (suc _) = false
_==fin_ {suc _} (suc _) zero = false
_==fin_ {suc _} (suc s) (suc t) = s ==fin t

transferFin : {n : ℕ} → (P : Fin n → Set) →
              (i j : Fin n) → T (i ==fin j) →
              P i → P j
transferFin {zero} P () j q p
transferFin {suc n} P zero zero q p = p
transferFin {suc n} P zero (suc j) () p
transferFin {suc n} P (suc i) zero () p
transferFin {suc n} P (suc i) (suc j) q p = transferFin {n} (P ∘ suc) i j q p

_==DecSets_ : {d : DecSets} → TDecSets d → TDecSets d  → Bool
_==DecSets_ {fin n} = _==fin_


transferFin' : {n : ℕ} → (P : Fin n → Set) →
              (i j : Fin n) → ((i ==fin j) ≡ true) →
              P i → P j
transferFin' {zero} P () j q p
transferFin' {suc n} P zero zero q p = p
transferFin' {suc n} P zero (suc j) () p
transferFin' {suc n} P (suc i) zero () p
transferFin' {suc n} P (suc i) (suc j) q p = transferFin' {n} (P ∘ suc) i j q p

transferDecSets : {J : DecSets} → (P : TDecSets J → Set) →
              (i j : TDecSets J) → ((i ==DecSets j) ≡ true) →
              P i → P j
transferDecSets {(fin n)} P i j q p = transferFin' {n} P i j q p


{-
transferDec : {J : DecSets} → (P : TDecSets J  → Set) →
              (i j : TDecSets) → ((i ==DecSets j) ≡ true) →
              P i → P j
-}


--with {!!} inspect {!!} --(_==DecSets_ j j')
--... | x = {!!}

{-
... | true = {!!} -- {!(I j).nextˢ (f j) m ?!}
... | false = {!!}
-}

{-
    = if (j ==DecSets j') then  else {!!}
-}


module _ (I : IOInterfaceˢ )
         (let S = IOStateˢ I) (let C = Commandˢ I)
         (let R = Responseˢ I) (let n = IOnextˢ I)
           where

  mutual

-- \writingOOsUsingIOVersFourReaderMethodsIOind
--@BEGIN@IOind
    data IOˢind (A : S → Set) (s : S) : Set where
--@C
      doˢ''      :  (c : C s) (f : (r : R s c) → IOˢind A (n s c r)) → IOˢind A s
      returnˢ''  :  (a : A s) → IOˢind A s
--@END






module _ {I : RInterfaceˢ } (let S = Stateˢ I) (let n = nextˢ I)
           where

-- \writingOOsUsingIOVersFourReaderMethodstranslateIOind
--@BEGIN@translateIOind
  translateˢ : {A : S → Set} (s : S) (obj : RObjectˢ I s) (p : IOˢind (objectInterfToIOInterfˢ I) A s)
               → Σ[ s′ ∈ S ]  (A s′ × RObjectˢ I s′)
  translateˢ s obj (returnˢ'' x)       =  s , (x , obj)
  translateˢ s obj (doˢ'' (inj₁ c) p)  = obj .objectMethod c ▹ λ {(x , o′) → translateˢ (n s c x) o′ (p x)  }
  translateˢ s obj (doˢ'' (inj₂ c) p)  = obj .readerMethod c ▹ λ x → translateˢ s obj (p x)
--@END
-- obj .objectMethod c ▹ λ {(x , o′)
--                                      → translateˢ {A} {n s c x} o′ (p x)  }


module _ {I : RInterfaceˢ }   (let S = Stateˢ I)
           where

  getAˢ : ∀{A : S → Set} (s : S)
               → RObjectˢ I s
               → IOˢind (objectInterfToIOInterfˢ I) A s
               → Σ[ s′ ∈ S ]  A s′
  getAˢ s obj (returnˢ'' x) =  s , x
  getAˢ s obj p             =  let  res = translateˢ s obj p
                               in   proj₁ res , proj₁ (proj₂ res)


module _ (I : IOInterfaceˢ )
         (let S = IOStateˢ I) (let C = Commandˢ I)
         (let R = Responseˢ I) (let n = IOnextˢ I)
           where

  mutual
    -- IOˢind' A sbegin send
    -- are programs which start in state sbegin and end in state send

    data IOˢind' (A : S → Set) (sbegin : S) : (send : S) → Set where

      doˢ'''     : {send : S} → (c : C sbegin)  →
                   (f : (r : R sbegin c) → IOˢind' A (n sbegin c r) send)
                  → IOˢind' A sbegin send
      returnˢ''' : (a : A sbegin) → IOˢind' A sbegin sbegin



module _ {I : RInterfaceˢ } (let S = Stateˢ I) (let n = nextˢ I)
           where

  translateˢ' : ∀{A : S → Set}{sbegin : S}{send : S}
               → RObjectˢ I sbegin
               → IOˢind' (objectInterfToIOInterfˢ I) A sbegin send
               → (A send × RObjectˢ I send)
  translateˢ' {A} {sbegin} {send} obj (returnˢ''' x) = x , obj
  translateˢ' {A} {sbegin} {send} obj (doˢ''' (inj₁ c) p) =
                   obj .objectMethod c ▹ λ {(x , o')
                   → translateˢ' {A} {n sbegin c x} {send} o' (p x)  }
  translateˢ' {A} {sbegin} {send} obj (doˢ''' (inj₂ c) p) =
                   obj .readerMethod c ▹ λ x
                   → translateˢ' {A} {sbegin} {send} obj (p x)

--                   obj .objectMethod c ▹ λ {(x , o')
--                   → translateˢ' {A} {n sbegin c x} {send} o' (p x)  }


module _ {I : RInterfaceˢ }   (let S = Stateˢ I)
           where

  getAˢ' : ∀{A : S → Set}{sbegin : S}{send : S}
               → RObjectˢ I sbegin
               → IOˢind' (objectInterfToIOInterfˢ I) A sbegin send
               → A send
  getAˢ' {A} {sbegin} {send} obj (returnˢ''' x) = x
  getAˢ' {A} {sbegin} {send} obj p = let res = translateˢ' {I} {A} {sbegin} {send} obj p
                        in proj₁ res




updateFinFunction : {n : ℕ} → (P : Fin n → Set)
                    → (f : (k : Fin n) → P k)
                    → (l : Fin n)
                    → (b : P l)
                    → (k : Fin n) → P k
updateFinFunction {zero} P f () b k
updateFinFunction {suc n} P f zero b zero = b
updateFinFunction {suc n} P f zero b (suc k) = f (suc k)
updateFinFunction {suc n} P f (suc l) b zero = f zero
updateFinFunction {suc n} P f (suc l) b (suc k) = updateFinFunction {n} (P ∘ suc)  (f ∘ suc) l b k

updateDecSetsFunction : {J : DecSets} → (P : TDecSets J → Set)
                    → (f : (k : TDecSets J) → P k)
                    → (l : TDecSets J)
                    → (b : P l)
                    → (k : TDecSets J) → P k
updateDecSetsFunction {fin n} P f l b k = updateFinFunction {n} P f l b k


updateFinFunctionStateChange : {n : ℕ}
                    → (P : Fin n → Set)
                    → (f : (k : Fin n) → P k)
                    → (Q : (k : Fin n) → P k → Set)
                    → (g : (k : Fin n) → Q k (f k) )
                    → (l : Fin n)
                    → (newP : P l)
                    → (newQ : Q l newP)
                    → (k : Fin n)
                    → Q k (updateFinFunction {n} P f l newP k)
updateFinFunctionStateChange {zero} P f Q g () newP newQ k
updateFinFunctionStateChange {suc n} P f Q g zero newP newQ zero = newQ
updateFinFunctionStateChange {suc n} P f Q g zero newP newQ (suc k) = g (suc k)
updateFinFunctionStateChange {suc n} P f Q g (suc l) newP newQ zero = g zero
updateFinFunctionStateChange {suc n} P f Q g (suc l) newP newQ (suc k) =
   updateFinFunctionStateChange {n} (P ∘ suc) (f ∘ suc)
                                (λ k p → Q (suc k) p)
                                (g ∘ suc) l newP newQ k


updateDecSetsFunctionStateChange : {J : DecSets}
                    → (P : TDecSets J → Set)
                    → (f : (k : TDecSets J) → P k)
                    → (Q : (k : TDecSets J) → P k → Set)
                    → (g : (k : TDecSets J) → Q k (f k) )
                    → (l : TDecSets J)
                    → (newP : P l)
                    → (newQ : Q l newP)
                    → (k : TDecSets J)
                    → Q k (updateDecSetsFunction {J} P f l newP k)
updateDecSetsFunctionStateChange {fin n} P f Q g l newP newQ k = updateFinFunctionStateChange {n} P f Q g l newP newQ k




objectInterfMultiToIOInterfˢ : (J : DecSets) → (TDecSets J → Interfaceˢ) → IOInterfaceˢ
objectInterfMultiToIOInterfˢ J I .IOStateˢ = (j : TDecSets J) →  (I j).Stateˢ
objectInterfMultiToIOInterfˢ J I .Commandˢ f  = Σ[ j ∈ TDecSets J ] (I j).Methodˢ (f j)
objectInterfMultiToIOInterfˢ J I .Responseˢ f (j , m) = (I j).Resultˢ (f j) m
objectInterfMultiToIOInterfˢ J I .IOnextˢ f (j , m) r =
   updateDecSetsFunction {J} (λ j₁ → I j₁ .Stateˢ) f j (I j .nextˢ (f j) m r)

{-
objectInterfMultiToIOInterfˢ J I .IOnextˢ f (j , m) r j' with (_==DecSets_ j j') | inspect (_==DecSets_ j) j'
... | true | [ eq ] = transferDecSets {J} (λ j'' → I j'' .Stateˢ) j j' eq ((I j).nextˢ (f j) m r)
... | false | [ eq ] = f j'
-}



translateMultiˢ : (J : DecSets) → (I : TDecSets J → Interfaceˢ) →
            (A : ((j : TDecSets J) →  (I j).Stateˢ) → Set)
            (f : (j : TDecSets J) →  (I j).Stateˢ)
            (obj : (j : TDecSets J) →  Objectˢ (I j) (f j))
             → IOˢind (objectInterfMultiToIOInterfˢ J I) A f
             → Σ[ s' ∈ ((j : TDecSets J) →  (I j).Stateˢ) ]
                (A s' × ( (j : TDecSets J) → Objectˢ (I j) (s' j)))
translateMultiˢ J I A f obj (doˢ'' (j , m) p) = (obj j) .objectMethod m ▹ λ {(r , o')
     → translateMultiˢ J I A (IOnextˢ (objectInterfMultiToIOInterfˢ J I) f (j , m) r)
        (updateDecSetsFunctionStateChange {J}
          (λ j₁ → I j₁ .Stateˢ)
          f
          (λ j₁ state → Objectˢ (I j₁) state)
          obj j
          (I j .nextˢ (f j) m r) o')
          (p r)}
translateMultiˢ J I A f obj (returnˢ'' a) = f , a , obj



module _ (I₁ : IOInterfaceˢ )
         (let S₁ = IOStateˢ I₁) (let C₁ = Commandˢ I₁)
         (let R₁ = Responseˢ I₁) (let n₁ = IOnextˢ I₁)
         (I₂ : IOInterfaceˢ )
         (let S₂ = IOStateˢ I₂)
         (let C₂ = Commandˢ I₂)
         (let R₂ = Responseˢ I₂)
         (let n₂ = IOnextˢ I₂)
           where

  mutual

--@BEGIN@defIoindcoind
    record  IOˢindcoind (i : Size)(A : S₁ → S₂ → Set) (s₁ : S₁)(s₂ : S₂) : Set where --@HIDE-BEG
      coinductive
      field
--@HIDE-END
            forceIC : {j : Size< i} → IOˢindcoind+ j A s₁ s₂

--@C     Note that in IOˢindcoind+
--@C               doˢobj  refers in f to IOˢindcoind+
--@C       whereas doˢIO   refers in f to IOˢindcoind
--@C
    data IOˢindcoind+ (i : Size)(A : S₁ → S₂ → Set) (s₁ : S₁)(s₂ : S₂) : Set where
       doˢIO      :  (c₁ : C₁ s₁) (f : (r₁ : R₁ s₁ c₁) → IOˢindcoind i A (n₁ s₁ c₁ r₁) s₂)
                     → IOˢindcoind+ i A s₁ s₂
       doˢobj     :  (c₂ : C₂ s₂)(f : (r₂ : R₂ s₂ c₂) → IOˢindcoind+ i A s₁ (n₂ s₂ c₂ r₂))
                     → IOˢindcoind+ i A s₁ s₂
       returnˢic  :  A s₁ s₂
                     → IOˢindcoind+ i A s₁ s₂
--@END
open IOˢindcoind public



module _ (I₁ : IOInterfaceˢ )
         (let S₁ = IOStateˢ I₁) (let C₁ = Commandˢ I₁)
         (let R₁ = Responseˢ I₁) (let n₁ = IOnextˢ I₁)
         (I₂ : IOInterfaceˢ )
         (let S₂ = IOStateˢ I₂)
         (let C₂ = Commandˢ I₂)
         (let R₂ = Responseˢ I₂)
         (let n₂ = IOnextˢ I₂) where

  ioˢind2IOˢindcoind+ : (A : S₁ → S₂ → Set) (s₁ : S₁)(s₂ : S₂)
                        (p : IOˢind I₂ (λ s₂' → A s₁ s₂') s₂)
                        → IOˢindcoind+ I₁ I₂ ∞ A s₁ s₂
  ioˢind2IOˢindcoind+ A s₁ s₂ (doˢ'' c f) = doˢobj c λ r →
                                            ioˢind2IOˢindcoind+ A s₁ (IOnextˢ I₂ s₂ c r) (f r)
  ioˢind2IOˢindcoind+ A s₁ s₂ (returnˢ'' a) = returnˢic a


  ioˢind2IOˢindcoind : (A : S₁ → S₂ → Set) (s₁ : S₁)(s₂ : S₂)
                        (p : IOˢind I₂ (λ s₂' → A s₁ s₂') s₂)
                        → IOˢindcoind I₁ I₂ ∞ A s₁ s₂

  ioˢind2IOˢindcoind A s₁ s₂ p .forceIC = ioˢind2IOˢindcoind+ A s₁ s₂ p


{-
    translateˢ : ∀{A : S → Set}{s : S}
                 → Objectˢ I s
                 → IOˢindcoind+ (objectInterfToIOInterfˢ I) A s
                 → Σ[ s' ∈ S ]  (A s' × Objectˢ I s')
    translateˢ {A} {s} obj (returnˢ'' x) = s , (x , obj)
    translateˢ {A} {s} obj (doˢobj c p) = obj .objectMethod c ▹ λ {(x , o')
                                        → translateˢ {A} {n s c x} o' (p x)  }
-}

{-
  delayˢic : {i : Size}{A : S₁ → S₂ → Set}{s₁ : S₁}{s₂ : S₂}
           → IOˢindcoindShape i A s₁ s₂
           → IOˢindcoind (↑ i) A s₁ s₂
  delayˢic {i} {A} {s₁} {s₂} P .IOˢindcoind.forceIC {j} = P
-}




module _ {I : IOInterfaceˢ } (let S = IOStateˢ I)
           where
   _>>=ind_ : {A :  S → Set}{B : S → Set}{s : S}
              (m : IOˢind I A s)
              (f : (s' : S) (a : A s') → IOˢind I B s')
              → IOˢind I B s
   _>>=ind_  (doˢ'' c f₁) f = doˢ'' c (λ r → f₁ r >>=ind f)
   _>>=ind_  {s = s} (returnˢ'' a) f = f s a



module _ {I₁ : IOInterfaceˢ }
         (let S₁ = IOStateˢ I₁) (let C₁ = Commandˢ I₁)
         (let R₁ = Responseˢ I₁) (let n₁ = IOnextˢ I₁)
         {I₂ : IOInterfaceˢ }
         (let S₂ = IOStateˢ I₂)
         (let C₂ = Commandˢ I₂)
         (let R₂ = Responseˢ I₂)
         (let n₂ = IOnextˢ I₂)
           where
   mutual
     _>>=indcoind+_ : {i : Size}{A : S₁ → S₂ → Set}
                      {B : S₁ → S₂ → Set}
                      {s₁ : S₁}{s₂ : S₂}
                      (p : IOˢindcoind+ I₁ I₂ i A s₁ s₂)
                      (f : {s₁' : S₁}{s₂' : S₂}(a : A s₁' s₂') → IOˢindcoind+ I₁ I₂ i B s₁' s₂')
                      → IOˢindcoind+ I₁ I₂ i B s₁ s₂
     doˢobj c f₁ >>=indcoind+ f = doˢobj c (λ r → f₁ r >>=indcoind+ f)
     doˢIO c f₁  >>=indcoind+ f = doˢIO c  (λ r → f₁ r >>=indcoind f)
     returnˢic x >>=indcoind+ f = f x


{-
     _>>=indcoindShape_ : {i : Size}{A : S₁ → S₂ → Set}
                      {B : S₁ → S₂ → Set}
                      {s₁ : S₁}{s₂ : S₂}
                      (p : IOˢindcoindShape I₁ I₂ i A s₁ s₂)
                      (f : (s₁' : S₁)(s₂' : S₂)(a : A s₁' s₂') → IOˢindcoind+ I₁ I₂ i B s₁' s₂')
                      → IOˢindcoind+ I₁ I₂ i B s₁ s₂
     doˢIO c₁ f₁ >>=indcoindShape f = returnˢ'' (doˢIO c₁ (λ r → f₁ r >>=indcoind f))
     _>>=indcoindShape_ {s₁ = s₁} {s₂ = s₂} (returnˢic x) f = x >>=indcoindaux' f
-}
     _>>=indcoind_ : {i : Size}{A : S₁ → S₂ → Set}
                      {B : S₁ → S₂ → Set}
                      {s₁ : S₁}{s₂ : S₂}
                      (p : IOˢindcoind I₁ I₂ i A s₁ s₂)
                      (f : {s₁' : S₁}{s₂' : S₂}(a : A s₁' s₂') → IOˢindcoind+ I₁ I₂ i B s₁' s₂')
                      → IOˢindcoind I₁ I₂ i B s₁ s₂
     (p >>=indcoind f) .forceIC {j} = p .forceIC >>=indcoind+ f


{-
     _>>=indcoindaux'_ : {i : Size}{A : S₁ → S₂ → Set}
                      {B : S₁ → S₂ → Set}
                      {s₁ : S₁}{s₂ : S₂}
                      (p : IOˢ' I₁ i (λ s₁' → A s₁' s₂) s₁)
                      (f : {s₁' : S₁}{s₂' : S₂}(a : A s₁' s₂') → IOˢindcoind+ I₁ I₂ i B s₁' s₂')
                      → IOˢindcoind+ I₁ I₂ i B s₁ s₂
     doˢ' c f₁ >>=indcoindaux' f = {!!} -- returnˢ'' (returnˢic (doˢ' c λ r → {!returnˢic!})) -- doˢ' c λ r → f₁ r >>=indcoindaux f
     _>>=indcoindaux'_ {s₁ = s₁}{s₂ = s₂} (returnˢ' a)  f = f {s₁} {s₂} a -- doˢobj {!inj₂ c!} {!!}
-}

{-
     _>>=indcoindaux_ : {i : Size}{A : S₁ → S₂ → Set}
                      {B : S₁ → S₂ → Set}
                      {s₁ : S₁}{s₂ : S₂}
                      (p : IOˢ I₁ i (λ s₁' → A s₁' s₂) s₁)
                      (f : (s₁' : S₁)(s₂' : S₂)(a : A s₁' s₂') → IOˢindcoind+ I₁ I₂ i B s₁' s₂')
                      → IOˢindcoind+ I₁ I₂ i B s₁ s₂
     p >>=indcoindaux f = {!!}
-}



module _ {I₁ : IOInterfaceˢ }
         (let S₁ = IOStateˢ I₁) (let C₁ = Commandˢ I₁)
         (let R₁ = Responseˢ I₁) (let n₁ = IOnextˢ I₁)
         {I₂ : IOInterfaceˢ }
         (let S₂ = IOStateˢ I₂)
           where
  open IOˢindcoind

  delayˢic : {i : Size}{A : S₁ → S₂ → Set}{s₁ : S₁}{s₂ : S₂}
           → IOˢindcoind+ I₁ I₂ i A s₁ s₂
           → IOˢindcoind I₁ I₂ (↑ i) A s₁ s₂
  delayˢic {i} {A} {s₁} {s₂} P .forceIC {j} = P



--Σ (Stateˢ I₂) (λ s₄ → Σ (A s₃ s₄) (λ x → Objectˢ I₂ s₄))) s₁


--→ IOˢind I₂ (λ s₂ → A s₁ s₂) s₂


open IOˢindcoind public


module _ (I₁ : IOInterfaceˢ )
         (let S₁ = IOStateˢ I₁) (let C₁ = Commandˢ I₁)
         (let R₁ = Responseˢ I₁) (let n₁ = IOnextˢ I₁)
         (I₂ : RInterfaceˢ )
         (let I₂′ = objectInterfToIOInterfˢ I₂)
         (let S₂ = Stateˢ I₂)(let n₂ = IOnextˢ I₂′)
           where
  mutual
--@BEGIN@translateIndCoindToIO
    translateˢIndCoind : ∀ {i A s₁ s₂} (obj : RObjectˢ I₂ s₂) (p : IOˢindcoind I₁ I₂′ i A s₁ s₂)
                       → IOˢ I₁ i (λ s₁ → Σ[ s₂ ∈ S₂ ] (A s₁ s₂ × RObjectˢ I₂ s₂)) s₁
    translateˢIndCoind obj p .forceˢ = translateˢIndCoind+ obj (p .forceIC)

    translateˢIndCoind+ : ∀{i A s₁ s₂} (obj : RObjectˢ  I₂ s₂) (p : IOˢindcoind+ I₁ I₂′ i A s₁ s₂)
                          → IOˢ' I₁ i (λ s₁ → Σ[ s₂ ∈ S₂ ] (A s₁ s₂ × RObjectˢ I₂ s₂)) s₁
    translateˢIndCoind+ obj (doˢobj (inj₁ c) f) = obj .objectMethod c ▹ λ { (x , obj′) →
      translateˢIndCoind+ obj′ (f x)}
    translateˢIndCoind+ obj (doˢobj (inj₂ c) f) = obj .readerMethod c ▹ λ x  →
      translateˢIndCoind+ obj (f x)
    translateˢIndCoind+ obj (doˢIO c₁ f) = doˢ' c₁ λ r₁ →
      translateˢIndCoind obj (f r₁)
    translateˢIndCoind+ {i} {A} {s₁} {s₂} obj (returnˢic a) = returnˢ' (s₂ , a , obj)
--@END
{-
    translateˢIndCoindShape : ∀{i} → {A : S₁ → S₂ → Set}{s₁ : S₁}{s₂ : S₂}
                 → RObjectˢ  I₂ s₂
                 → IOˢindcoindShape I₁ I₂′ i A s₁ s₂
                 → IOˢ' I₁ i ((λ s₁ → Σ[ s₂ ∈ S₂ ]  (A s₁ s₂ × RObjectˢ I₂ s₂))) s₁
    translateˢIndCoindShape {i} {A} {.s₁} {.s₂} obj (doˢIO {s₁} {s₂} c₁ p)
           = doˢ' c₁ (λ r₁ → translateˢIndCoind {i} {A} {n₁ s₁ c₁ r₁} {s₂} obj (p r₁))
    translateˢIndCoindShape {i} {A} {.s₁} {.s₂} obj (returnˢic {s₁} {s₂} p)
           = fmapˢ' i (λ s a → ( s₂ , a , obj)) s₁ p
-}



---
--- ### file content of writingOOsUsingIO
---


{-
objectInterfMultiToIOInterfˢ J I .IOnextˢ f (j , m) r j' with (_==DecSets_ j j') | inspect (_==DecSets_ j) j'
... | true | [ eq ] = transferDecSets {J} (λ j'' → I j'' .Stateˢ) j j' eq ((I j).nextˢ (f j) m r)
... | false | [ eq ] = f j'
-}




module _ (I₁ : IOInterfaceˢ )
         (let S₁ = IOStateˢ I₁) (let C₁ = Commandˢ I₁)
         (let R₁ = Responseˢ I₁) (let n₁ = IOnextˢ I₁)
         (I₂ : IOInterfaceˢ )
         (let S₂ = IOStateˢ I₂)
           where







unsizedIOInterfToIOInterfˢ : IOInterface → IOInterfaceˢ
unsizedIOInterfToIOInterfˢ x .IOStateˢ  = Unit
unsizedIOInterfToIOInterfˢ x .Commandˢ  = λ _ → x .Command
unsizedIOInterfToIOInterfˢ x .Responseˢ = λ _ → x .Response
unsizedIOInterfToIOInterfˢ x .IOnextˢ   _ _ _ =  unit

ConsoleInterfaceˢ : IOInterfaceˢ
ConsoleInterfaceˢ = unsizedIOInterfToIOInterfˢ consoleI



data RCellStateˢ  : Set where
  empty full  : RCellStateˢ

data RCellMethodEmpty (A : Set) : Set where
    put : A → RCellMethodEmpty A

data RCellMethodFull (A : Set)  : Set where
    put : A → RCellMethodFull A


data RRCellMethodEmpty (A : Set) : Set where

data RRCellMethodFull (A : Set)  : Set where
    get : RRCellMethodFull A


RCellMethodˢ : (A : Set) → RCellStateˢ → Set
RCellMethodˢ A empty = RCellMethodEmpty A
RCellMethodˢ A full = RCellMethodFull A

RRCellMethodˢ : (A : Set) → RCellStateˢ → Set
RRCellMethodˢ A empty = RRCellMethodEmpty A
RRCellMethodˢ A full = RRCellMethodFull A

putGen : {A : Set} → {i : RCellStateˢ} → A → RCellMethodˢ A i
putGen {A} {empty} = put
putGen {A} {full} = put


RCellResultFull : ∀{A} → RCellMethodFull A → Set
RCellResultFull (put _) = Unit

RCellResultEmpty : ∀{A} → RCellMethodEmpty A → Set
RCellResultEmpty (put _) = Unit


RRCellResultFull : ∀{A} → RRCellMethodFull A → Set
RRCellResultFull {A} get = A

RRCellResultEmpty : ∀{A} → RRCellMethodEmpty A → Set
RRCellResultEmpty ()


RCellResultˢ : (A : Set) → (s : RCellStateˢ) → RCellMethodˢ A s → Set
RCellResultˢ A empty = RCellResultEmpty{A}
RCellResultˢ A full = RCellResultFull{A}

RRCellResultˢ : (A : Set) → (s : RCellStateˢ) → RRCellMethodˢ A s → Set
RRCellResultˢ A empty = RRCellResultEmpty{A}
RRCellResultˢ A full = RRCellResultFull{A}


nˢ : ∀{A} → (s : RCellStateˢ) → (c : RCellMethodˢ A s) → (RCellResultˢ A s c) → RCellStateˢ
nˢ _ _ _ = full

RCellInterfaceˢ : (A : Set) → RInterfaceˢ
Stateˢ (RCellInterfaceˢ A)  = RCellStateˢ
Methodˢ (RCellInterfaceˢ A)  = RCellMethodˢ A
Resultˢ (RCellInterfaceˢ A)  = RCellResultˢ A
RMethodˢ (RCellInterfaceˢ A)  = RRCellMethodˢ A
RResultˢ (RCellInterfaceˢ A)  = RRCellResultˢ A
nextˢ (RCellInterfaceˢ A)  = nˢ

{-
mutual
   RcellPempty : (i : Size) → IOObject consoleI (RCellInterfaceˢ String) i empty
   method (cellPempty i) {j} (put str) = do (putStrLn ("put (" ++ str ++ ")")) λ _ →
                                         return (unit , cellPfull j str)

   cellPfull : (i : Size) → (str : String) → IOObject consoleI (CellInterfaceˢ String) i full
   method (cellPfull i str) {j} get        = do (putStrLn ("get (" ++ str ++ ")")) λ _ →
                                             return (str , cellPfull j str)
   method (cellPfull i str) {j} (put str') = do (putStrLn ("put (" ++ str' ++ ")")) λ _ →
                                             return (unit , cellPfull j str')
-}

-- UNSIZED Version, without IO
mutual
   RcellPempty' : ∀{A} → RObjectˢ (RCellInterfaceˢ A) empty
   RcellPempty' .objectMethod (put a)     =  (_ , RcellPfull' a)
   RcellPempty' .readerMethod ()

   RcellPfull' : ∀{A} → A → RObjectˢ (RCellInterfaceˢ A) full
   RcellPfull' a .readerMethod get         = a
   RcellPfull' a .objectMethod (put a')  = (_ , RcellPfull' a')


RCellInterfaceˢIO : IOInterfaceˢ
RCellInterfaceˢIO = objectInterfToIOInterfˢ (RCellInterfaceˢ String)



module _ (I : IOInterface)
       (let C = I .Command)
       (let R = I .Response)
       (let I' = unsizedIOInterfToIOInterfˢ I)
       (let C' = I' .Commandˢ)
       (let R' = I' .Responseˢ)
       (convertC : C' _ → C)
       (convertR : ∀{c : C} → Response I (convertC c)  →  I .Response c)

       where
  mutual

    flatternIOˢ : ∀ {A : Set}
                 → IOˢ (unsizedIOInterfToIOInterfˢ I) ∞ (λ _ → A) unit
                 → IO I ∞ A
    flatternIOˢ {A} p .force  = flatternIOˢ' (forceˢ p)


    flatternIOˢ' : {A : Set}
                 → IOˢ' (unsizedIOInterfToIOInterfˢ I) ∞ (λ _ → A) unit
                 → IO' I ∞ A
    flatternIOˢ' {A} (doˢ' cˢ f) = do' (convertC cˢ) (λ rˢ →
                    flatternIOˢ (f (convertR {cˢ} rˢ)))
    flatternIOˢ' {A} (returnˢ' a) = return' a



{-
doIOShape : {i : Size}
       {I₁ :  IOInterfaceˢ} {I₂ :  IOInterfaceˢ}
       {A : I₁ .IOStateˢ → I₂ .IOStateˢ → Set}
       {s₁ : I₁ .IOStateˢ}
       {s₂ : I₂ .IOStateˢ}
      (c₁ : I₁ .Commandˢ s₁) →
         ((r₁ : I₁ .Responseˢ s₁ c₁) →
          IOˢindcoind I₁ I₂ i  A (IOnextˢ I₁ s₁ c₁ r₁) s₂)
        →  IOˢindcoindShape I₁ I₂ i A  s₁ s₂
doIOShape  = doˢIO
-}

{-
callMethod'' : {I₂ :  IOInterfaceˢ}
             {A : I₂ .IOStateˢ → Set}
             {s₂ : I₂ .IOStateˢ}
             (c : Commandˢ I₂ s₂) →
             ((r : Responseˢ I₂ s₂ c) → IOˢind I₂ A (IOnextˢ I₂ s₂ c r))
             → IOˢind I₂ A s₂
callMethod'' = doˢobj
-}

doˢobj∞ : {I₁ : IOInterfaceˢ }{I₂ :  IOInterfaceˢ}
             {A : IOStateˢ I₁ → I₂ .IOStateˢ → Set}
             {s₁ : IOStateˢ I₁}
             {s₂ : I₂ .IOStateˢ}
             (c : Commandˢ I₂ s₂) →
             ((r : Responseˢ I₂ s₂ c) → IOˢindcoind+ I₁ I₂ ∞ A s₁ (IOnextˢ I₂ s₂ c r) )
             → IOˢindcoind I₁ I₂ ∞ A s₁ s₂
doˢobj∞ {I₁} {I₂} {A} {s₁} {s₂} c f .forceIC {j} = doˢobj c  f

{-
callMethod+ : {I₁ : IOInterfaceˢ }{I₂ :  IOInterfaceˢ}
             {A : IOStateˢ I₁ → I₂ .IOStateˢ → Set}
             {s₁ : IOStateˢ I₁}
             {s₂ : I₂ .IOStateˢ}
             (c : Commandˢ I₂ s₂) →
             ((r : Responseˢ I₂ s₂ c) → IOˢindcoind+ I₁ I₂ ∞ A s₁ (IOnextˢ I₂ s₂ c r) )
             → IOˢindcoind+ I₁ I₂ ∞ A s₁ s₂
callMethod+ {I₁} {I₂} {A} {s₁} {s₂} = doˢobj
-}

{-
we think not needed anymore
endIO : {I₁ :  IOInterfaceˢ} {I₂ :  IOInterfaceˢ}
--      {A : I₁ .IOStateˢ → I₂ .IOStateˢ → Set}
       {s₁ : I₁ .IOStateˢ}
       {s₂ : I₂ .IOStateˢ}
       → IOˢind I₂ (λ s → IOˢindcoind I₁ I₂ ∞ (λ _ _ → Unit) s₁ s) s₂
endIO {I₁} {I₂} {s₁} {s₂} = returnˢ'' (delayˢic (returnˢ'' (returnˢic (returnˢ' unit)))) -- (delayˢic (returnˢic (returnˢ' unit)))
--                returnˢ'' {I₂}
--             {!!} -- (delayˢic {!returnˢ''!} ) -- (returnˢ'' (returnˢic (returnˢ' unit))))   --(returnˢic (returnˢ' unit)))
-}


endIO+ : {I₁ :  IOInterfaceˢ} {I₂ :  IOInterfaceˢ}
       {s₁ : I₁ .IOStateˢ}
       {s₂ : I₂ .IOStateˢ}
       → IOˢindcoind+ I₁ I₂ ∞ (λ _ _ → Unit) s₁ s₂
endIO+ = returnˢic unit

endIO∞ : {I₁ :  IOInterfaceˢ} {I₂ :  IOInterfaceˢ}
       {s₁ : I₁ .IOStateˢ}
       {s₂ : I₂ .IOStateˢ}
       → IOˢindcoind I₁ I₂ ∞ (λ _ _ → Unit) s₁ s₂
endIO∞ .forceIC {j} = endIO+


doˢIO∞ : {i : Size}
        {I₁ :  IOInterfaceˢ} {I₂ :  IOInterfaceˢ}
       {s₁ : I₁ .IOStateˢ}
       {s₂ : I₂ .IOStateˢ}
       (c₁ : I₁ .Commandˢ s₁) →
       ((r₁ : I₁ .Responseˢ s₁ c₁) →
        IOˢindcoind I₁ I₂ i (λ _ _ → Unit) (IOnextˢ I₁ s₁ c₁ r₁) s₂)
       → IOˢindcoind I₁ I₂ i (λ _ _ → Unit) s₁ s₂
doˢIO∞ {i} c p .forceIC {j} = doˢIO c p



callProg : {I : IOInterfaceˢ }{A : I .IOStateˢ → Set}{s : I .IOStateˢ} (a : A s) → IOˢind I A s
callProg = returnˢ''



run' : IOˢindcoind ConsoleInterfaceˢ RCellInterfaceˢIO ∞ (λ x y → Unit)
          unit empty
       → NativeIO Unit
run' prog = translateIOConsole
               (flatternIOˢ  consoleI (λ c → c) (λ r → r)
              (fmapˢ ∞ (λ x y → unit) unit
                (translateˢIndCoind ConsoleInterfaceˢ
                                    (RCellInterfaceˢ String) RcellPempty' (prog))))

module _ {objInf : RInterfaceˢ}
         (let objIOInf = objectInterfToIOInterfˢ objInf)
         {objState : objIOInf .IOStateˢ }
           where
--@BEGIN@defRunStratingWith
        run_startingWith_ :  IOˢindcoind ConsoleInterfaceˢ objIOInf ∞ (λ x y → Unit) unit objState
                             → RObjectˢ objInf objState → NativeIO Unit
--@END@
        run prog startingWith obj = translateIOConsole
           (flatternIOˢ  consoleI (λ c → c) (λ r → r) (fmapˢ ∞ (λ x y → unit) unit
                                    (translateˢIndCoind ConsoleInterfaceˢ objInf obj prog)))


        run+_startingWith_ : IOˢindcoind+ ConsoleInterfaceˢ objIOInf ∞ (λ _ _ → Unit) unit objState
              → RObjectˢ objInf objState
              → NativeIO Unit
        run+ prog startingWith obj = translateIOConsole
                         (flatternIOˢ consoleI id id (fmapˢ ∞  (λ _ _ → unit) unit
                              (delayˢ (translateˢIndCoind+ ConsoleInterfaceˢ  objInf obj prog))))
-- (ioInterfToObjectInterfˢ objIOInf)
--- ### END of file content of writingOOsUsingIO
---


{-

obj .objectMethod c ▹ λ {(x , o')
                                      → translateˢ {A} {n s c x} o' (p x)  }


                              let q : Σ[ s' ∈ S₂ ]
                                        (IOˢindcoindShape I₁ I₂′ i A s₁ s'
                                         × Objectˢ I₂ s')
                                  q = translateˢ obj p
                              in translateˢIndCoindShape (proj₂ (proj₂ q)) (proj₁ (proj₂ q)) -}




module _ (I₁ : IOInterfaceˢ )
         (let S₁ = IOStateˢ I₁) (let C₁ = Commandˢ I₁)
         (let R₁ = Responseˢ I₁) (let n₁ = IOnextˢ I₁)
         (I₂ : IOInterfaceˢ )
         (let S₂ = IOStateˢ I₂)
         (let C₂ = Commandˢ I₂)
         (let R₂ = Responseˢ I₂)
         (let n₂ = IOnextˢ I₂)
         (I₂' : IOInterface)
         (let C₂' = I₂' .Command)
         (let R₂' = I₂' .Response)
         (let I₂'' = unsizedIOInterfToIOInterfˢ I₂')
         (let C₂'' = I₂'' .Commandˢ)
         (let R₂'' = I₂'' .Responseˢ)
         (convertC : (s₂ : S₂)(c₂ : C₂ s₂) → C₂')
         (convertR : (s₂ : S₂)(c₂ : C₂ s₂)(r₂ : R₂' (convertC s₂ c₂)) → R₂ s₂ c₂)
         (A : Set)
           where

   mutual
    translateIndCoindFlatteningObj : ∀{i} (s₁ : S₁) (s₂ : S₂)
                                       → IOˢindcoind I₁ I₂ i (λ _ _ →  A) s₁ s₂
                                       → IOˢindcoind I₁ I₂'' i (λ _ _ →  A) s₁ _
    translateIndCoindFlatteningObj {i} s₁ s₂ p .forceIC {j} = translateIndCoindFlatteningObj+ {j} s₁ s₂ (p .forceIC {j})

    translateIndCoindFlatteningObj+ : ∀{i} (s₁ : S₁) (s₂ : S₂)
                                       → IOˢindcoind+ I₁ I₂ i (λ _ _ →  A) s₁ s₂
                                       → IOˢindcoind+ I₁ I₂'' i (λ _ _ →  A) s₁ _
    translateIndCoindFlatteningObj+ {i} s₁ s₂ (doˢIO c₁ f) = doˢIO c₁ λ r₁ → translateIndCoindFlatteningObj (n₁ s₁ c₁ r₁) s₂ (f r₁)
    translateIndCoindFlatteningObj+ {i} s₁ s₂ (doˢobj c₂ f) = doˢobj (convertC s₂ c₂) λ r₂ →
                                                              translateIndCoindFlatteningObj+ s₁ (n₂ s₂ c₂ (convertR s₂ c₂ r₂)) (f (convertR s₂ c₂ r₂))
    translateIndCoindFlatteningObj+ {i} s₁ s₂ (returnˢic x) = returnˢic x
