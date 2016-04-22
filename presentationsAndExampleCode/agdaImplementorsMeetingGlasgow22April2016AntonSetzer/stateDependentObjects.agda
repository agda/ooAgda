module stateDependentObjects where

open import Size renaming (Size to AgdaSize)
open import Agda.Builtin.Equality
open import Data.Nat.Base as N hiding (_⊔_)
open import Data.Product
open import Data.Vec as Vec using (Vec; []; _∷_; head; tail)
open import Function
open import NativeIO
open import Relation.Binary.PropositionalEquality
open import interactiveProgramsAgda 
-- open import SizedIO.Base

{- State dependent interfaces, objects -}

record Interfaceˢ : Set₁ where
  field  Stateˢ  : Set
         Methodˢ : (s : Stateˢ) → Set
         Resultˢ : (s : Stateˢ) → (m : Methodˢ s) → Set
         nextˢ   : (s : Stateˢ) → (m : Methodˢ s) → (r : Resultˢ s m) 
                   → Stateˢ

open Interfaceˢ public

{- State-Dependent Objects -}

record Objectˢ (I : Interfaceˢ) (s : Stateˢ I) : Set where
  coinductive
  field objectMethod :  (m : Methodˢ I s) →
                        Σ[ r ∈ Resultˢ I s m ] Objectˢ I (nextˢ I s m r)

open Objectˢ public

record IOObjectˢ (Iᵢₒ : IOInterface) (I : Interfaceˢ) (s : Stateˢ I) : Set where
  coinductive
  field method :  (m : Methodˢ I s) →
                  IO Iᵢₒ ∞ (Σ[ r ∈ Resultˢ I s m ] IOObjectˢ Iᵢₒ I (nextˢ I s m r))


{- Example of a Stack -}

StackStateˢ : Set
StackStateˢ = ℕ

data StackMethodˢ (A : Set) : (n : StackStateˢ) → Set where
  push  :  ∀ {n}  →  A  →  StackMethodˢ A n
  pop   :  ∀ {n}         →  StackMethodˢ A (suc n)


StackResultˢ : (A : Set) → (s : StackStateˢ) → StackMethodˢ A s → Set
StackResultˢ A _  (push _)  =  Unit
StackResultˢ A _  pop       =  A

stackNextˢ  :  ∀ A n (m : StackMethodˢ A n) (r : StackResultˢ A n m) →  StackStateˢ
stackNextˢ A  n        (push x)  r  =  suc n
stackNextˢ A  (suc n)  pop       r  =  n

StackInterfaceˢ : (A : Set)  →  Interfaceˢ
Stateˢ   (StackInterfaceˢ A)  =  StackStateˢ
Methodˢ  (StackInterfaceˢ A)  =  StackMethodˢ A
Resultˢ  (StackInterfaceˢ A)  =  StackResultˢ A
nextˢ    (StackInterfaceˢ A)  =  stackNextˢ A


stack  :  ∀{A}{n : ℕ} (as : Vec A n) →  Objectˢ (StackInterfaceˢ A) n
objectMethod (stack as)        (push a)  =  _  ,  stack (a ∷ as)
objectMethod (stack (a ∷ as))  pop       =  a  ,  stack as



{- Reasoning about Stateful Objects -}

{- Bisimiliarity -}

module Bisim (I : Interfaceˢ)
             (let S = Stateˢ I)   (let M = Methodˢ I) (let R = Resultˢ I)
             (let next = nextˢ I) (let O = Objectˢ I) 
  where

  data  ΣR     {A : Set} {B : A → Set} (R : ∀{a} (b b' : B a) → Set)
               :  (p p' : Σ A B) → Set
        where
        eqΣ    :  ∀{a}{b b' : B a} → R b b' → ΣR R (a , b) (a , b')


  record _≅_ {s : S} (o o' : O s) : Set where
    coinductive
    field  bisimMethod  :  (m : M s) →
                           ΣR (_≅_) (objectMethod o m) (objectMethod o' m)

  open _≅_ public


  refl≅ :  ∀{s} (o : O s) → o ≅ o
  bisimMethod (refl≅ o) m  =  let  (r , o') =  objectMethod o m
                              in   eqΣ (refl≅ o')



module _ {E : Set} where
  private
    I = StackInterfaceˢ E
    S = Stateˢ I
    O = Objectˢ I
  open Bisim I



{-  Verifying Stack laws -}

  pop-after-push : ∀{n} {v : Vec E n} {e : E} →
    let  st          =  stack v
         (_ , st₁)   =  objectMethod  st   (push e)
         (e₂ , st₂)  =  objectMethod  st₁  pop

    in   (e ≡ e₂) × (st ≅ st₂)

  pop-after-push = refl , refl≅ _
  
  push-after-pop : ∀{n} {v : Vec E n} {e : E} →
    let  st            =  stack (e ∷ v)
         (e₁  ,  st₁)  =  objectMethod st   pop
         (_   ,  st₂)  =  objectMethod st₁  (push e₁)

    in   st ≅ st₂
  push-after-pop = refl≅ _


{- Bisimilarity of different stack implementations -}

  stackFState = ℕ → E

  pushStackF : E → stackFState → stackFState
  pushStackF e f = λ { 0       → e ; 
                       (suc m) → f m}

  popStackFe : stackFState → E 
  popStackFe f = f 0  

  popStackFf  :  stackFState → stackFState 
  popStackFf f = f ∘ suc  

  tabulate  :  ∀ (n : ℕ) → stackFState → Vec E n
  tabulate  0        f  =  []
  tabulate  (suc n)  f  =  popStackFe f ∷ tabulate n (popStackFf f)

  stackF : ∀ (n : ℕ) (f : ℕ → E) → Objectˢ (StackInterfaceˢ E) n
  objectMethod (stackF n       f) (push e) = _ , 
                                             stackF (suc n) (pushStackF e f)
  objectMethod (stackF (suc n) f) pop      = popStackFe f , 
                                             stackF n (popStackFf f)


  impl-bisim : ∀{n f} v (p : tabulate n f ≡ v) → stackF n f ≅ stack v
  bisimMethod (impl-bisim v        p) (push e) =
    eqΣ (impl-bisim (e ∷ v)  (cong (_∷_ e)  p))

  bisimMethod (impl-bisim (e ∷ v)  p) pop rewrite cong head p =
    eqΣ (impl-bisim v        (cong tail     p))



