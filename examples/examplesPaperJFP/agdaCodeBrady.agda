{-#  OPTIONS --type-in-type #-}
module examplesPaperJFP.agdaCodeBrady where



open import Data.List
open import Agda.Builtin.Unit public renaming (⊤ to Unit; tt to triv)
open import Data.Product
open import examplesPaperJFP.StateDependentIO

{- Brady's Effect -}

Effect : Set₁
Effect = (Result : Set) → (InResource : Set) →  (OutResource : Result → Set) → Set


record MyEffect : Set₁ where
  field  Ops          :  Set
         Result       :  Ops → Set
         InResource   :  Ops → Set
         OutResource  :  (o : Ops) → Result o → Set

open MyEffect

effectToIOInterfaceˢ : Effect → IOInterfaceˢ
Stateˢ     (effectToIOInterfaceˢ  eff)     =  Set
Commandˢ   (effectToIOInterfaceˢ  eff)  s  =
                   Σ[ Result ∈ Set ] (Σ[ outR ∈ (Result → Set) ] (eff Result s outR))
Responseˢ  (effectToIOInterfaceˢ  eff)  s (result , outR , op)  =  result
nextˢ      (effectToIOInterfaceˢ  eff)  s (result , outR , op)  =  outR

const : { A B  : Set} → B → A → B
const b = λ _ → b

data EFFECT′ : Set₁  where
  MkEff : Set → Effect → EFFECT′

EFFECT : Set₁
EFFECT = Set × Effect


data State : Effect where
  Get : (a : Set) → State   a    a (λ _ →  a)
  Put : (a : Set) → (b : Set) → State a a (λ _ → b)

data myStateOps : Set₁ where
  get :  Set → myStateOps
  put : Set → Set → myStateOps

myState : MyEffect
Ops myState            = myStateOps
Result myState (get a) = a
InResource myState (get a) = a
OutResource myState (get a) _ = a
Result myState (put a b) = a
InResource myState (put a b) = a
OutResource myState (put a b) _ = b

STATE : Set → EFFECT
STATE x = ( x , State )

postulate String : Set

data Stdio : Effect where
  PutStr : String → Stdio Unit Unit (const Unit)
  GetStr : Stdio String  String (const String)

STDIO : EFFECT
STDIO = ( Unit , Stdio )

data Eff : (x : Set) → List EFFECT → (x → List EFFECT) → Set where
  get : (x : Set) → Eff x [ STATE x ] (const [ STATE x ])
  put : (x : Set) → x → Eff Unit [ STATE x ] (const [ STATE x  ])
  putM : (x : Set) → (y : Set) → y → Eff Unit [ STATE x ] (const  [ STATE y ])
  update : (x : Set) → (x → x) → Eff Unit [ STATE x ] (const [ STATE x ])


data EffM : (m : Set → Set) → (res : Set) →
            (inEffects : List EFFECT) →
            (outEffects : res → List EFFECT)
            → Set where
   _>>=_ : {m : Set → Set} → {res : Set} →
           {inEffects : List EFFECT} →
            {outEffects : res → List EFFECT} →
            {res′ : Set} →
            {inEffects′ : res → List EFFECT} →
            {outEffects′ : res′  → List EFFECT} →
            EffM m res inEffects outEffects →
            ((x : res) → EffM m res′ (inEffects′ x) outEffects′) →
            EffM m res′ inEffects outEffects′

record SetInterfaceˢ : Set where
  field  Commandˢ′  :  Set → Set
         Responseˢ′ :  (s : Set) → Commandˢ′ s → Set
         nextˢ′     :  (s : Set) → (c : Commandˢ′ s) → Responseˢ′ s c → Set

open SetInterfaceˢ

module _  (I   : SetInterfaceˢ ) (let Stateˢ = Set)
          (let C  = Commandˢ′ I) (let  R  = Responseˢ′ I)
          (let next = nextˢ′ I) where
  handle :  (M : Set → Set) → Set
  handle M =
     (A : Set) → (s : Stateˢ)  → (c : C s) →  (f : (r : R s c) → next s c r → M A) → M A

postulate Char : Set
