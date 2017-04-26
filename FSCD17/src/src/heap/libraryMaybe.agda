module src.heap.libraryMaybe where

open import Data.Maybe hiding (maybe)
open import Data.Empty
open import Data.Unit.Base
open import Data.Product renaming (proj₁ to pr₁; proj₂ to pr₂; _×_ to _×'_; map to mapp)

data NativeMaybe (A : Set) : Set where
  nothingNative : NativeMaybe A
  justNative : A → NativeMaybe A

{-# COMPILE GHC NativeMaybe = data Maybe (Nothing | Just) #-}

nativeMaybeFunc : {A : Set} {B : Set} → (A → B) → NativeMaybe A → NativeMaybe B
nativeMaybeFunc f (justNative x) = justNative (f x)
nativeMaybeFunc f nothingNative = nothingNative

{-# INLINE nativeMaybeFunc #-}

maybeFunc : {A : Set} {B : Set} → (A → B) → Maybe A → Maybe B
maybeFunc f (just x) = just (f x)
maybeFunc f nothing = nothing
{-# INLINE maybeFunc #-}

IsNothing : {A : Set} (a : Maybe A) →  Set
IsNothing (just x) = ⊥
IsNothing nothing = ⊤

NothingInductionLemma : ∀{A}(P : Maybe A → Set) → (a : Maybe A) -> IsNothing a → P nothing → P a
NothingInductionLemma p (just x) ()
NothingInductionLemma p nothing q q' = q'

{-
NothingMaybeLem : {A B : Set} → (P : B → Set) → (a : Maybe A)
                  → IsNothing a
                  → (g : A → B)
                  → (b : B)
                  → P b
                  → P (maybe g b a)
NothingMaybeLem P (just x) () b g p
NothingMaybeLem P nothing anothing b g p = p
-}

maybeAcrossBtoMaybeAcrossB : {A B : Set} (mab : Maybe A ×' B) → Maybe (A ×' B)
maybeAcrossBtoMaybeAcrossB (just a , b) = just (a , b)
maybeAcrossBtoMaybeAcrossB (nothing , _) = nothing

maybeFunctor : {A B : Set} (f : A → B) (ma : Maybe A) → Maybe B
maybeFunctor f (just x) = just (f x)
maybeFunctor f nothing = nothing
