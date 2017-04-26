--@PREFIX@heapAsObject
{-# OPTIONS --postfix-projections #-}


module src.heap.heapAsObjectBase where


open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (_∘_)

open import Data.Bool.Base using (T; Bool)
open import Data.Fin using (Fin; toℕ; suc; zero)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc) renaming (_⊔_ to _⊔n_)

open import Data.Product using () renaming (proj₁ to pr₁; proj₂ to pr₂; _×_ to _×'_)

open import heap.libraryNat


World : Set
World = ℕ


sucw : World → World
sucw  = suc

-- Kind of heap element types.


--@BEGIN@WorldPred
record WorldPred :  Set₁ where  --@HIDE-BEG
 constructor _,,,_
 field

   -- Type of heap elmenents at world w.
--@HIDE-END
   El    :  (w : World) → Set
--@C
--@C    Casting to extended world.
   lift  :  (w : World) (x : El w) → El (sucw w)
--@END
open WorldPred public

-- Lifting heap element type to next world.

liftWorldPred : WorldPred → WorldPred
El (liftWorldPred pred)     = pred .El ∘ suc
lift (liftWorldPred pred) w = lift pred (suc w)

_≦w_ : World → World → Bool
w ≦w w'  = w ≦ℕb w'

refl≦ℕw : (n : ℕ) → T (n ≦w n)
refl≦ℕw  = refl≦ℕb





Pointer : World → Set
Pointer = Fin

new : {w : World} → Pointer (sucw w)
new  = zero

embed : (w : World) → Pointer w → Pointer (suc w)
embed w = suc

membed : (w : World) → Maybe (Pointer w) → Maybe (Pointer (suc w))
membed w (just x) = just (suc x)
membed w nothing = nothing

embedImplicit : {w : World} → Pointer w → Pointer (suc w)
embedImplicit {w} = suc

embed+ : (w : World) → Pointer w → (w' : World) → T (w ≦w w')
         → Pointer w'
embed+ w p w' ww' = leqEmbedLem Pointer embed w w' ww' p

lift+ : (wp : WorldPred) → (w w' : World) →  T (w ≦w w') →  wp .El w → wp .El w'
lift+ wp = leqEmbedLem (wp .El) (lift wp)



record Heap (wp : WorldPred)  (w : World) : Set where
   field
       ↑ : Pointer w → wp .El w

open Heap public

liftHeap : {wp : WorldPred} {w : World} (h : Heap wp (suc w)) → Heap (liftWorldPred wp) w
↑ (liftHeap {wp} {w} h) p = ↑ h (suc p)

newH : {wp : WorldPred} →
       {w : World} → Heap wp w → wp .El (sucw w) → Heap wp (sucw w)
↑ (newH h a) zero = a
↑ (newH {wp} {w} h a) (suc x) = lift wp w (↑ h x)



writeH : {wp : WorldPred} → {w : World} → Heap wp w → Pointer w →  wp .El w
        → Heap wp w
↑ (writeH h zero a) zero = a
↑ (writeH h zero a) (suc q) = ↑ h (suc q)
↑ (writeH h (suc p) a) zero = ↑ h zero
↑ (writeH {wp} h (suc p) a) (suc q) = ↑ (writeH {liftWorldPred wp} (liftHeap h) p a) q


writeH+ : {wp : WorldPred} → {w : World} → Heap wp w →
          {w' : ℕ} → {w'w : T (w' ≦w w)} →  Pointer w' →  wp .El w → Heap wp w
writeH+ {wp} {w} h {w'} {w'w} p a = writeH {wp} {w} h (embed+ w' p w w'w) a



↑+ : {wp : WorldPred} →  {w' : World} → Heap wp w'
              →  {w : World} → {ww' : T (w  ≦w w')} → Pointer w → wp .El w'
↑+ {wp} {w'} h {w} {ww'} p = ↑ {wp} {w'} h (embed+ w p w' ww')


∅w : World
∅w = 0

∅H : ∀ {wp : WorldPred} → Heap wp ∅w
↑ ∅H ()


_==p_ : {w w' : World} → Pointer w → Pointer w' → Set
_==p_ {w} {w'} p p' = embed+ w p (w ⊔n w') (⊔isMaxl {w} {w'})
                       ≡ embed+ w' p' (w ⊔n w') (⊔isMaxr {w} {w'})

_==pb_ : {w w' : World} → Pointer w → Pointer w' → Bool
_==pb_ {w} {w'} p p' = toℕ (embed+ w p (w ⊔n w') (⊔isMaxl {w} {w'}))
                       ==b toℕ (embed+ w' p' (w ⊔n w') (⊔isMaxr {w} {w'}))


_==wp_ : {wp : WorldPred} → {w w' : World} → wp .El w → wp .El w' → Set
_==wp_ {wp} {w} {w'} p p' = lift+ wp w (w ⊔n w') (⊔isMaxl {w} {w'}) p
                           ≡
                           lift+ wp w' (w ⊔n w') (⊔isMaxr {w} {w'}) p'
