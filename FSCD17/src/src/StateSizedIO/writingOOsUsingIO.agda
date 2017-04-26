{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --allow-unsolved-metas #-}


module src.StateSizedIO.writingOOsUsingIO where


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
open import src.SizedIO.Console hiding (main;translateIOConsole)
open import Size
open import src.SizedIO.Base
open import src.StateSizedIO.cellStateDependent
open import src.NativeIO


--
-- Delete this file (all stuff moved to writingOOsUsingIOVers2.agda
--
{-
objectInterfToIOInterfˢ : Interfaceˢ → IOInterfaceˢ
objectInterfToIOInterfˢ I .IOStateˢ = I .Stateˢ
objectInterfToIOInterfˢ I .Commandˢ = I .Methodˢ
objectInterfToIOInterfˢ I .Responseˢ = I .Resultˢ
objectInterfToIOInterfˢ I .IOnextˢ = I .nextˢ


ioInterfToObjectInterfˢ : IOInterfaceˢ → Interfaceˢ
ioInterfToObjectInterfˢ I .Stateˢ = I .IOStateˢ
ioInterfToObjectInterfˢ I .Methodˢ = I .Commandˢ
ioInterfToObjectInterfˢ I .Resultˢ = I .Responseˢ
ioInterfToObjectInterfˢ I .nextˢ = I .IOnextˢ


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

    data IOˢind (A : S → Set) (s : S) : Set where

      doˢ''     : (c : C s) (f : (r : R s c) → IOˢind A (n s c r)) → IOˢind A s
      returnˢ'' : (a : A s) → IOˢind A s



module _ {I : Interfaceˢ } (let S = Stateˢ I) (let n = nextˢ I)
           where

  translateˢ : ∀{A : S → Set}{s : S}
               → Objectˢ I s
               → IOˢind (objectInterfToIOInterfˢ I) A s
               → Σ[ s' ∈ S ]  (A s' × Objectˢ I s')
  translateˢ {A} {s} obj (returnˢ'' x) = s , (x , obj)
  translateˢ {A} {s} obj (doˢ'' c p) = obj .objectMethod c ▹ λ {(x , o')
                                      → translateˢ {A} {n s c x} o' (p x)  }


module _ {I : Interfaceˢ }   (let S = Stateˢ I)
           where

  getAˢ : ∀{A : S → Set}{s : S}
               → Objectˢ I s
               → IOˢind (objectInterfToIOInterfˢ I) A s
               → Σ[ s' ∈ S ]  A s'
  getAˢ {A} {s} obj (returnˢ'' x) = s , x
  getAˢ {A} {s} obj p = let res = translateˢ {I} {A} {s} obj p
                        in proj₁ res , proj₁ (proj₂ res)


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



module _ {I : Interfaceˢ } (let S = Stateˢ I) (let n = nextˢ I)
           where

  translateˢ' : ∀{A : S → Set}{sbegin : S}{send : S}
               → Objectˢ I sbegin
               → IOˢind' (objectInterfToIOInterfˢ I) A sbegin send
               → (A send × Objectˢ I send)
  translateˢ' {A} {sbegin} {send} obj (returnˢ''' x) = x , obj
  translateˢ' {A} {sbegin} {send} obj (doˢ''' c p) = obj .objectMethod c ▹ λ {(x , o')
                                      → translateˢ' {A} {n sbegin c x} {send} o' (p x)  }

module _ {I : Interfaceˢ }   (let S = Stateˢ I)
           where

  getAˢ' : ∀{A : S → Set}{sbegin : S}{send : S}
               → Objectˢ I sbegin
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
           where

  mutual
    IOˢindcoind+ : (i : Size)(A : S₁ → S₂ → Set) (s₁ : S₁)(s₂ : S₂) → Set
    IOˢindcoind+ i A s₁ s₂ = IOˢind I₂ ((λ s₂ → IOˢindcoind i A s₁ s₂)) s₂

    record IOˢindcoind (i : Size)(A : S₁ → S₂ → Set) (s₁ : S₁)(s₂ : S₂) : Set where
      coinductive
      field
        forceIC : {j : Size< i} → IOˢindcoindShape j A s₁ s₂




    data IOˢindcoindShape (i : Size)(A : S₁ → S₂ → Set) : S₁ → S₂ → Set where
      doˢic : {s₁ : S₁} → {s₂ : S₂} → (c₁ : C₁ s₁)
           → ((r₁ : R₁ s₁ c₁) → IOˢindcoind+ i A (n₁ s₁ c₁ r₁) s₂)
           → IOˢindcoindShape i A s₁ s₂
      returnˢic : {s₁ : S₁} →  {s₂ : S₂}
                 → IOˢ' I₁ i (λ s₁' → A s₁' s₂) s₁
                 → IOˢindcoindShape i A s₁ s₂

{-
  delayˢic : {i : Size}{A : S₁ → S₂ → Set}{s₁ : S₁}{s₂ : S₂}
           → IOˢindcoindShape i A s₁ s₂
           → IOˢindcoind (↑ i) A s₁ s₂
  delayˢic {i} {A} {s₁} {s₂} P .IOˢindcoind.forceIC {j} = P
-}



module _ {I₁ : IOInterfaceˢ }
         (let S₁ = IOStateˢ I₁) (let C₁ = Commandˢ I₁)
         (let R₁ = Responseˢ I₁) (let n₁ = IOnextˢ I₁)
         {I₂ : IOInterfaceˢ }
         (let S₂ = IOStateˢ I₂)
           where
  open IOˢindcoind

  delayˢic : {i : Size}{A : S₁ → S₂ → Set}{s₁ : S₁}{s₂ : S₂}
           → IOˢindcoindShape I₁ I₂ i A s₁ s₂
           → IOˢindcoind I₁ I₂ (↑ i) A s₁ s₂
  delayˢic {i} {A} {s₁} {s₂} P .forceIC {j} = P


--Σ (Stateˢ I₂) (λ s₄ → Σ (A s₃ s₄) (λ x → Objectˢ I₂ s₄))) s₁


--→ IOˢind I₂ (λ s₂ → A s₁ s₂) s₂


open IOˢindcoind public

module _ (I₁ : IOInterfaceˢ )
         (let S₁ = IOStateˢ I₁) (let C₁ = Commandˢ I₁)
         (let R₁ = Responseˢ I₁) (let n₁ = IOnextˢ I₁)
         (I₂ : Interfaceˢ )
         (let I₂' = objectInterfToIOInterfˢ I₂)
         (let S₂ = Stateˢ I₂)(let n₂ = IOnextˢ I₂')
           where
  mutual

    translateˢIndCoind+ : ∀{i} → {A : S₁ → S₂ → Set}{s₁ : S₁}{s₂ : S₂}
                 → Objectˢ  I₂ s₂
                 → IOˢindcoind+ I₁ I₂' i A s₁ s₂
                 → IOˢ I₁ i ((λ s₁ → Σ[ s₂ ∈ S₂ ]  (A s₁ s₂ × Objectˢ I₂ s₂))) s₁
    translateˢIndCoind+ {i} {A} {s₁} {s₂} obj p =
                              let q : Σ[ s' ∈ S₂ ]
                                        (IOˢindcoind I₁ I₂' i A s₁ s'
                                         × Objectˢ I₂ s')
                                  q = translateˢ obj p
                              in translateˢIndCoind (proj₂ (proj₂ q)) (proj₁ (proj₂ q))

    translateˢIndCoind : ∀{i} → {A : S₁ → S₂ → Set}{s₁ : S₁}{s₂ : S₂}
                 → Objectˢ  I₂ s₂
                 → IOˢindcoind I₁ I₂' i A s₁ s₂
                 → IOˢ I₁ i ((λ s₁ → Σ[ s₂ ∈ S₂ ]  (A s₁ s₂ × Objectˢ I₂ s₂))) s₁ --
    translateˢIndCoind {i} {A} {s₁} {s₂} obj p .forceˢ {j}
             = translateˢIndCoind' {j} {A} {s₁} {s₂} obj (p .forceIC {j})


    translateˢIndCoind' : ∀{i} → {A : S₁ → S₂ → Set}{s₁ : S₁}{s₂ : S₂}
                 → Objectˢ  I₂ s₂
                 → IOˢindcoindShape I₁ I₂' i A s₁ s₂
                 → IOˢ' I₁ i ((λ s₁ → Σ[ s₂ ∈ S₂ ]  (A s₁ s₂ × Objectˢ I₂ s₂))) s₁
    translateˢIndCoind' {i} {A} {.s₁} {.s₂} obj (doˢic {s₁} {s₂} c₁ p)
           = doˢ' c₁ (λ r₁ → translateˢIndCoind+ {i} {A} {n₁ s₁ c₁ r₁} {s₂} obj (p r₁))
    translateˢIndCoind' {i} {A} {.s₁} {.s₂} obj (returnˢic {s₁} {s₂} p)
           = fmapˢ' i (λ s a → ( s₂ , a , obj)) s₁ p


unsizedIOInterfToIOInterfˢ : IOInterface → IOInterfaceˢ
unsizedIOInterfToIOInterfˢ x .IOStateˢ  = Unit
unsizedIOInterfToIOInterfˢ x .Commandˢ  = λ _ → x .Command
unsizedIOInterfToIOInterfˢ x .Responseˢ = λ _ → x .Response
unsizedIOInterfToIOInterfˢ x .IOnextˢ   _ _ _ =  unit

ConsoleInterfaceˢ : IOInterfaceˢ
ConsoleInterfaceˢ = unsizedIOInterfToIOInterfˢ consoleI

CellInterfaceˢIO : IOInterfaceˢ
CellInterfaceˢIO = objectInterfToIOInterfˢ (CellInterfaceˢ String)



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




doIO : {i : Size}
       {I₁ :  IOInterfaceˢ} {I₂ :  IOInterfaceˢ}
       {A : I₁ .IOStateˢ → I₂ .IOStateˢ → Set}
       {s₁ : I₁ .IOStateˢ}
       {s₂ : I₂ .IOStateˢ}
      (c₁ : I₁ .Commandˢ s₁) →
         ((r₁ : I₁ .Responseˢ s₁ c₁) →
          IOˢindcoind+ I₁ I₂ i  A (IOnextˢ I₁ s₁ c₁ r₁) s₂)
        →  IOˢindcoindShape I₁ I₂ i A  s₁ s₂
doIO  = doˢic

callMethod : {I₂ :  IOInterfaceˢ}
             {A : I₂ .IOStateˢ → Set}
             {s₂ : I₂ .IOStateˢ}(c : Commandˢ I₂ s₂) →
               ((r : Responseˢ I₂ s₂ c) → IOˢind I₂ A (IOnextˢ I₂ s₂ c r)) →
               IOˢind I₂ A s₂
callMethod = doˢ''



endIO : {I₁ :  IOInterfaceˢ} {I₂ :  IOInterfaceˢ}
--      {A : I₁ .IOStateˢ → I₂ .IOStateˢ → Set}
       {s₁ : I₁ .IOStateˢ}
       {s₂ : I₂ .IOStateˢ}
       → IOˢind I₂ (λ s → IOˢindcoind I₁ I₂ ∞ (λ _ _ → Unit) s₁ s) s₂
endIO {I₁} {I₂} {s₁} {s₂} = returnˢ'' (delayˢic (returnˢic (returnˢ' unit)))
--                returnˢ'' {I₂}
--             {!!} -- (delayˢic {!returnˢ''!} ) -- (returnˢ'' (returnˢic (returnˢ' unit))))   --(returnˢic (returnˢ' unit)))

endIO+ : {I₁ :  IOInterfaceˢ} {I₂ :  IOInterfaceˢ}
--      {A : I₁ .IOStateˢ → I₂ .IOStateˢ → Set}
       {s₁ : I₁ .IOStateˢ}
       {s₂ : I₂ .IOStateˢ}
       → IOˢindcoind+ I₁ I₂ ∞ (λ _ _ → Unit) s₁ s₂
endIO+ = returnˢ'' (delayˢic (returnˢic (returnˢ' unit))) -- (returnˢic (returnˢ' unit))


doIO+ : {i : Size}
        {I₁ :  IOInterfaceˢ} {I₂ :  IOInterfaceˢ}
--       {A : I₁ .IOStateˢ → I₂ .IOStateˢ → Set}
       {s₁ : I₁ .IOStateˢ}
       {s₂ : I₂ .IOStateˢ}
       (c₁ : I₁ .Commandˢ s₁) →
       ((r₁ : I₁ .Responseˢ s₁ c₁) →
        IOˢindcoind+ I₁ I₂ i (λ _ _ → Unit) (IOnextˢ I₁ s₁ c₁ r₁) s₂)
       → IOˢindcoind+ I₁ I₂ i (λ _ _ → Unit) s₁ s₂
doIO+ {i} c p = returnˢ'' (delayˢic (doˢic c (λ r → p r)))


doIO+' : {i : Size}
        {I₁ :  IOInterfaceˢ} {I₂ :  IOInterfaceˢ}
       {s₁ : I₁ .IOStateˢ}
       {s₂ : I₂ .IOStateˢ}
       (c₁ : I₁ .Commandˢ s₁) →
       ((r₁ : I₁ .Responseˢ s₁ c₁) →
        IOˢindcoind I₁ I₂ i (λ _ _ → Unit) (IOnextˢ I₁ s₁ c₁ r₁) s₂)
       → IOˢindcoind+ I₁ I₂ i (λ _ _ → Unit) s₁ s₂
doIO+' {i} c p = returnˢ'' (delayˢic (doˢic c (λ r → returnˢ'' (p r)))) -- p r -- (doˢic c ? ) -- )


callProg : {I : IOInterfaceˢ }{A : I .IOStateˢ → Set}{s : I .IOStateˢ} (a : A s) → IOˢind I A s
callProg = returnˢ''



run' : IOˢindcoind ConsoleInterfaceˢ CellInterfaceˢIO ∞ (λ x y → Unit)
          unit empty
       → NativeIO Unit
run' prog = translateIOConsole
               (flatternIOˢ  consoleI (λ c → c) (λ r → r)
              (fmapˢ ∞ (λ x y → unit) unit
                (translateˢIndCoind ConsoleInterfaceˢ
                                    (CellInterfaceˢ String) cellPempty' (prog))))


module _ {objInf : Interfaceˢ}
         (let objIOInf = objectInterfToIOInterfˢ objInf)
         {objState : objIOInf .IOStateˢ }
           where

        run_startingWith_ : IOˢindcoind ConsoleInterfaceˢ objIOInf ∞ (λ x y → Unit) unit objState
              → Objectˢ objInf objState
              → NativeIO Unit
        run prog startingWith obj = translateIOConsole
           (flatternIOˢ  consoleI (λ c → c) (λ r → r) (fmapˢ ∞ (λ x y → unit) unit
                                    (translateˢIndCoind ConsoleInterfaceˢ objInf obj prog)))


        run+_startingWith_ : IOˢindcoind+ ConsoleInterfaceˢ objIOInf ∞ (λ x y → Unit) unit objState
              → Objectˢ objInf objState
              → NativeIO Unit
        run+ prog startingWith obj = translateIOConsole
           (flatternIOˢ  consoleI (λ c → c) (λ r → r) (fmapˢ ∞ (λ x y → unit) unit
                     (delayˢ (forceˢ (translateˢIndCoind+ ConsoleInterfaceˢ (ioInterfToObjectInterfˢ objIOInf) obj prog)))))
-}
