--@PREFIX@correctnessLinkedListVersSixStepTwoVersOne
{-# OPTIONS --postfix-projections #-}


module examples.heap.correctnessLinkedListStep2 where

open import Relation.Binary.PropositionalEquality hiding (sym)


open import Relation.Binary.PropositionalEquality hiding (sym)
--open import Relation.Binary.HeterogeneousEquality hiding (cong;sym)
open import Relation.Nullary


open import Function

open import Data.Bool.Base
open import Data.String
open import Data.Empty
open import Data.Fin hiding (lift)
open import Data.Maybe hiding (maybe)
-- open import Data.Maybe -- renaming (map to maybefunc)
open import Data.Nat hiding (_≟_) renaming (_⊔_ to _⊔n_)
open import Data.List
open import Data.Product renaming (proj₁ to pr₁; proj₂ to pr₂; _×_ to _×'_)
open import Data.Unit hiding ( _≟_ )

open import Level renaming (zero to lzero; suc to lsuc) hiding (lift)
open import Size hiding (↑_)
open import Data.Sum

open import heap.libraryNat
open import heap.libraryBool
open import heap.library

open import SizedIO.Base
--open import StateSizedIO.Object  renaming (objectMethod to method)


{-open import UnSizedIO.Object renaming (objectMethod to method)
open import StateSizedIO.Object  renaming (objectMethod to method) -}
open import StateSizedIO.Base

open import NativeIO

open import src.heap.heapAsObjectBase  hiding (Pointer;newH)
open import src.heap.heapAsObjectGeneric

open import StateSizedIO.writingOOsUsingIOVers4ReaderMethods hiding (nˢ)

open import SizedIO.Console using (putStrLn; getLine)

open import SizedIO.Console using (consoleI; translateIOConsoleLocal)
open import src.heap.worldModule

open import Data.Bool.Base
open import Data.Empty renaming (⊥-elim to efq)
open import Data.Fin hiding (lift)

open import Data.Nat hiding (_≟_) renaming (_⊔_ to _⊔n_)
open import Data.Product renaming (proj₁ to pr₁; proj₂ to pr₂; _×_ to _×'_; map to mapp)
open import Data.Unit hiding ( _≟_ )
open import Data.List

open import heap.libraryNat
open import heap.libraryMaybe
open import heap.libraryFin
open import heap.libraryBool
open import heap.library

open import StateSizedIO.RObject renaming (objectMethod to method)

--open import UnSizedIO.Object renaming (objectMethod to method)
open import SizedIO.Object renaming (objectMethod to method)

open import StateSizedIO.Object  renaming (objectMethod to method)

open import src.heap.heapAsObject hiding (readP;writeP)

open import StateSizedIO.writingOOsUsingIO

--open import src.heap.ExampleHeapAsObject
open import Function

open import examples.heap.correctnessLinkedList


open  moduleHeapDef

module _ (B : Set) (pS : PointerStruct) where
  open heapObjectLLMod B pS public




module _ (pointStruct : PointerStruct)
         (let Pointer = Pointer pointStruct)
         (let embedp = embedp pointStruct) where

  heapInterfaceGen : (B : Set) → IOInterfaceˢ
  heapInterfaceGen B =  HeapInterfaceˢIO Pointer (gLinkedWP B pointStruct)


  nilHeapProg : {B : Set}{w : World} →
                IOˢind (heapInterfaceGen B) (λ w' → Maybe (Pointer w')) w
  nilHeapProg = returnˢ'' nothing


  nilHeapaux : {B : Set}{w : World} →
            (heap : HeapObjectLL B pointStruct w)
            → Σ[ w' ∈ World ] (Maybe (Pointer w') ×' HeapObjectLL B pointStruct w')
  nilHeapaux {B}{w} heap =  translateˢ {HeapRInterfaceˢ Pointer (gLinkedWP B pointStruct)}
                               {λ w' → Maybe (Pointer w')} w heap (nilHeapProg {B})

  nilHeapauxWorld : {B : Set}{w : World} →
                    (heap : HeapObjectLL B pointStruct w)
                    → World
  nilHeapauxWorld {B} {w} heap = pr₁ (nilHeapaux {B} {w} heap)

  nilHeapauxWorldIsw : {B : Set}{w : World}(heap : HeapObjectLL B pointStruct w)
                        →  nilHeapauxWorld {B} {w} heap ≡ w
  nilHeapauxWorldIsw {B} {w} heap = refl

  nilHeapauxPointer : {B : Set}{w : World}
                      (heap : HeapObjectLL B pointStruct w)
                      → Maybe (Pointer w)
  nilHeapauxPointer {B} {w} heap = pr₁ (pr₂ (nilHeapaux {B} {w} heap))

  nilHeapauxHeap : {B : Set}{w : World}(heap : HeapObjectLL B pointStruct w)
                      → HeapObjectLL B pointStruct w
  nilHeapauxHeap {B} {w} heap = pr₂ (pr₂ (nilHeapaux {B} {w} heap))


-- \correctnessLinkedListVersSixStepTwoVersOne
--@BEGIN@consHeapProg
  consHeapProg : ∀ B {w} (b : B) (mp : Maybe (Pointer w)) →
                IOˢind (heapInterfaceGen B) (λ w' → w' ≡ sucw w  ×' Pointer w') w
  consHeapProg B b p  =  doˢ'' (inj₁ (newPh (linkedListNode b (membedp B pointStruct p)))) λ q →
                         returnˢ'' (refl , q)
--@END

  consHeapProgIndCoind : ∀ B {w} (b : B) (mp : Maybe (Pointer w)) →
                IOˢindcoind ConsoleInterfaceˢ (heapInterfaceGen B) ∞ (λ _ w' → w' ≡ sucw w  ×' Pointer w') _ w
-- \correctnessLinkedListVersSixStepTwoVersOne
--@BEGIN@consHeapProgIndCoind
  consHeapProgIndCoind B {w} b mp = ioˢind2IOˢindcoind ConsoleInterfaceˢ
                                        (heapInterfaceGen B)
                                        (λ _ w' → w' ≡ sucw w  ×' Pointer w') _ w (consHeapProg B {w} b mp)
--@END

  consHeapProgIndCoind+ : (B : Set){w : World} (b : B)(mp : Maybe (Pointer w)) →
                IOˢindcoind+ ConsoleInterfaceˢ (heapInterfaceGen B) ∞ (λ _ w' → w' ≡ sucw w  ×' Pointer w') _ w
  consHeapProgIndCoind+ B {w} b mp = ioˢind2IOˢindcoind+ ConsoleInterfaceˢ
                                        (heapInterfaceGen B)
                                        (λ _ w' → w' ≡ sucw w  ×' Pointer w') _ w (consHeapProg B {w} b mp)

  consHeapaux : (B : Set){w : World}(b : B)(mp : Maybe (Pointer w)) →
            (heap : HeapObjectLL B pointStruct w)
            → Σ[ w' ∈ World ] ((w' ≡ sucw w  ×' Pointer w') ×' HeapObjectLL B pointStruct w')
  consHeapaux B {w} b mp heap =  translateˢ {HeapRInterfaceˢ Pointer (gLinkedWP B pointStruct)}
                               {λ w' → w' ≡ sucw w  ×' Pointer w'} w heap (consHeapProg B{w} b mp)

  consHeapauxWorld : (B : Set){w : World}(b : B)(mp : Maybe (Pointer w)) →
                    (heap : HeapObjectLL B pointStruct w)
                    → World
  consHeapauxWorld B b mp heap = pr₁ (consHeapaux B b mp heap)

  consHeapauxWorldIsw : (B : Set){w : World}(b : B)(mp : Maybe (Pointer w))(heap : HeapObjectLL B pointStruct w)
                        →  consHeapauxWorld B {w} b  mp heap ≡ sucw w
  consHeapauxWorldIsw B b mp heap = refl

  consHeapauxPointer : (B : Set){w : World}(b : B)(mp : Maybe (Pointer w))
                      (heap : HeapObjectLL B pointStruct w)
                      → Pointer (sucw w)
  consHeapauxPointer B b mp heap = pr₂ (pr₁ (pr₂ (consHeapaux B b mp heap)))

  consHeapauxHeap : (B : Set){w : World}(b : B)(mp : Maybe (Pointer w))
                      (heap : HeapObjectLL B pointStruct w)
                      → HeapObjectLL B pointStruct (sucw w)
  consHeapauxHeap B b mp heap = pr₂ (pr₂ (consHeapaux B b mp heap))


  headHeapProg : {B : Set}{w : World} (mp : Maybe (Pointer w)) →
                IOˢind (heapInterfaceGen B) (λ w' →  w' ≡ w ×' Maybe B) w
  headHeapProg {B} {w} (just p) = doˢ'' (inj₂ (readPh p)) λ q →
                                 returnˢ'' (refl , just (q .getElemLL))
  headHeapProg {B} {w} nothing = returnˢ'' (refl , nothing)

  headHeapProgIndCoind : {B : Set}{w : World} (mp : Maybe (Pointer w)) →
                IOˢindcoind ConsoleInterfaceˢ (heapInterfaceGen B) ∞ (λ _ w' → w' ≡ w ×' Maybe B) _ w
  headHeapProgIndCoind {B} {w} mp = ioˢind2IOˢindcoind ConsoleInterfaceˢ
                                        (heapInterfaceGen B)
                                        (λ _ w' → w' ≡ w ×' Maybe B) _ w (headHeapProg {B} {w} mp)

  headHeapProgIndCoind+ : {B : Set}{w : World} (mp : Maybe (Pointer w)) →
                IOˢindcoind+ ConsoleInterfaceˢ (heapInterfaceGen B) ∞ (λ _ w' → w' ≡ w ×' Maybe B) _ w
  headHeapProgIndCoind+ {B} {w} mp = ioˢind2IOˢindcoind+ ConsoleInterfaceˢ
                                        (heapInterfaceGen B)
                                        (λ _ w' → w' ≡ w ×' Maybe B) _ w (headHeapProg {B} {w} mp)



  headHeapaux : {B : Set}{w : World} (mp : Maybe (Pointer w)) →
            (heap : HeapObjectLL B pointStruct w)
            → Σ[ w' ∈ World ] ((w' ≡ w ×'  Maybe B) ×' HeapObjectLL B pointStruct w')
  headHeapaux {B}{w} mp heap =  translateˢ {HeapRInterfaceˢ Pointer (gLinkedWP B pointStruct)}
                               {λ w' → w' ≡ w ×' Maybe B} w heap (headHeapProg {B}{w} mp )

  headHeapauxWorld : {B : Set}{w : World} (mp : Maybe (Pointer w))(heap : HeapObjectLL B pointStruct w)
                    → World
  headHeapauxWorld {B} {w} mp heap = pr₁ (headHeapaux {B} {w} mp heap)

  headHeapauxWorldIsw : {B : Set}{w : World}(mp : Maybe (Pointer w))(heap : HeapObjectLL B pointStruct w)
                        →  headHeapauxWorld {B} {w} mp heap ≡ w
  headHeapauxWorldIsw {B} {w} (just x) heap = refl
  headHeapauxWorldIsw {B} {w} nothing heap = refl

  headHeapauxItem : {B : Set}{w : World}(mp : Maybe (Pointer w)) (heap : HeapObjectLL B pointStruct w)
                      → Maybe B
  headHeapauxItem {B} {w} mp heap = pr₂ (pr₁ (pr₂ (headHeapaux {B} {w} mp heap)))





  tailHeapProg : {B : Set}{w : World} (p : Pointer w) →
                IOˢind (heapInterfaceGen B) (λ w' →  w' ≡ w ×' Maybe (Pointer w')) w
  tailHeapProg {B} {w} p = doˢ'' (inj₂ (readPh p)) λ q →
                                 returnˢ'' (refl , q .getNextLL)


  tailHeapProgIndCoind : {B : Set}{w : World} (p : Pointer w) →
                IOˢindcoind ConsoleInterfaceˢ (heapInterfaceGen B) ∞ (λ _ w' → w' ≡ w ×' Maybe (Pointer w')) _ w
  tailHeapProgIndCoind {B} {w} p = ioˢind2IOˢindcoind ConsoleInterfaceˢ
                                        (heapInterfaceGen B)
                                        (λ _ w' → w' ≡ w ×' Maybe (Pointer w')) _ w (tailHeapProg {B} {w} p)

  tailHeapProgIndCoind+ : {B : Set}{w : World} (p : Pointer w) →
                IOˢindcoind+ ConsoleInterfaceˢ (heapInterfaceGen B) ∞ (λ _ w' → w' ≡ w ×' Maybe (Pointer w')) _ w
  tailHeapProgIndCoind+ {B} {w} p = ioˢind2IOˢindcoind+ ConsoleInterfaceˢ
                                        (heapInterfaceGen B)
                                        (λ _ w' → w' ≡ w ×' Maybe (Pointer w')) _ w (tailHeapProg {B} {w} p)



  tailHeapaux : {B : Set}{w : World} (p : Pointer w) →
            (heap : HeapObjectLL B pointStruct w)
            → Σ[ w' ∈ World ] ((w' ≡ w ×' Maybe (Pointer w')) ×' HeapObjectLL B pointStruct w')
  tailHeapaux {B}{w} p heap =  translateˢ {HeapRInterfaceˢ Pointer (gLinkedWP B pointStruct)}
                               {λ w' → w' ≡ w ×' Maybe (Pointer w')} w heap (tailHeapProg {B}{w} p )



  tailHeapauxWorld : {B : Set}{w : World} (p : Pointer w)(heap : HeapObjectLL B pointStruct w)
                    → World
  tailHeapauxWorld {B} {w} p heap = pr₁ (tailHeapaux {B} {w} p heap)

  tailHeapauxWorldIsw : {B : Set}{w : World}(p : Pointer w)(heap : HeapObjectLL B pointStruct w)
                        →  tailHeapauxWorld {B} {w} p heap ≡ w
  tailHeapauxWorldIsw {B} {w} p heap = refl



  tailHeapauxPointer : {B : Set}{w : World}(p : Pointer w) (heap : HeapObjectLL B pointStruct w)
                      → Maybe (Pointer w)
  tailHeapauxPointer {B} {w} p heap = pr₂ (pr₁ (pr₂ (tailHeapaux {B} {w} p heap)))

  tailHeapauxHeap : {B : Set}{w : World}(p : Pointer w) (heap : HeapObjectLL B pointStruct w)
                      → HeapObjectLL B pointStruct w
  tailHeapauxHeap {B} {w} p heap = pr₂ (pr₂ (tailHeapaux {B} {w} p heap))




{-

  -- the following code works but is no longer used


  tailHeapProg' : {B : Set}{w : World} (mp : Maybe (Pointer w)) →
                IOˢind (heapInterfaceGen B) (λ w' →  Maybe (Maybe (Pointer w))) w
  tailHeapProg' {B} {w} (just p) = doˢ'' (inj₂ (readPh p)) λ q →
                                 returnˢ'' (just (q .getNextLL))
  tailHeapProg' {B} {w} nothing = returnˢ'' nothing



  tailHeapaux' : {B : Set}{w : World} (mp : Maybe (Pointer w)) →
            (heap : HeapObjectLL B pointStruct w)
            → Σ[ w' ∈ World ] (Maybe (Maybe (Pointer w)) ×' HeapObjectLL B pointStruct w')
  tailHeapaux' {B}{w} mp heap =  translateˢ {HeapRInterfaceˢ Pointer (gLinkedWP B pointStruct)}
                               {λ w' → Maybe (Maybe (Pointer w))}{w} heap (tailHeapProg' {B}{w} mp )



  tailHeapauxWorld' : {B : Set}{w : World} (mp : Maybe (Pointer w))(heap : HeapObjectLL B pointStruct w)
                    → World
  tailHeapauxWorld' {B} {w} mp heap = pr₁ (tailHeapaux' {B} {w} mp heap)

  tailHeapauxWorldIsw' : {B : Set}{w : World}(mp : Maybe (Pointer w))(heap : HeapObjectLL B pointStruct w)
                        →  tailHeapauxWorld' {B} {w} mp heap ≡ w
  tailHeapauxWorldIsw' {B} {w} (just x) heap = refl
  tailHeapauxWorldIsw' {B} {w} nothing heap = refl
-}






open heapRObjectFinM


startHeap : {B : Set} → HeapObjectLL B pointerStructfin ∅w
startHeap {B} = heapRObject (gLinkedWP B pointerStructfin) ∅Hfin

nillFromProg : (B : Set) → HeapWithPointer B {∅w}
nillFromProg B .llheap = nilHeapauxHeap pointerStructfin {B} {∅w} (startHeap {B})
nillFromProg B .llpoint = nilHeapauxPointer pointerStructfin {B} {∅w} (startHeap {B})

nillFromProg=Nill : (B : Set) → nillFromProg B ≡ nill B
nillFromProg=Nill B = refl


consFromProgaux : (B : Set){w : World}(b : B)(heap : HeapObjectLL B pointerStructfin w)(mp : MPointerfin w)
                   → HeapWithPointer B {sucw w}
consFromProgaux B {w} b heap mp .llheap = consHeapauxHeap pointerStructfin B {w} b mp heap
consFromProgaux B {w} b heap mp .llpoint = just (consHeapauxPointer pointerStructfin B {w} b mp heap)



consFromProg : (B : Set){w : World}(b : B)(heapWithPoin : HeapWithPointer B {w})
                   → HeapWithPointer B {sucw w}
consFromProg B {w} b heapWithPoin = consFromProgaux B {w} b (heapWithPoin .llheap) (heapWithPoin .llpoint)


consFromProgCor : (B : Set){w : World}(b : B)(heapWithPoin : HeapWithPointer B {w})
                   → consFromProg B {w} b heapWithPoin ≡ cons B {w} b heapWithPoin
consFromProgCor B {w} b heapWithPoin = refl




headFromProg : (B : Set){w : World}(heapWithPoin : HeapWithPointer B {w})
                   → Maybe B
headFromProg B {w} heapWithPoin = headHeapauxItem pointerStructfin {B} {w} (heapWithPoin .llpoint) (heapWithPoin .llheap)

headFromProgCoraux : (B : Set){w : World}(llp : MPointerfin w)(llh : heapObjectLLMod.HeapObjectLL B pointerStructfin w)
                   → headFromProg B {w} (llist llh llp) ≡ head B {w} (llist llh llp)
headFromProgCoraux B {w} (just x) llh = refl
headFromProgCoraux B {w} nothing llh = refl

headFromProgCor : (B : Set){w : World}(heapWithPoin : HeapWithPointer B {w})
                   → headFromProg B {w} heapWithPoin ≡ head B {w} heapWithPoin
headFromProgCor B {w} (llist llheap₁ llpoint₁) = headFromProgCoraux B {w} llpoint₁ llheap₁

tailFromProgaux : (B : Set){w : World}(llheap : HeapObjectLL B pointerStructfin w)
                                      (mp     : MPointerfin w)
                   → Maybe (HeapWithPointer B {w})
tailFromProgaux B {w} heap (just p) = just (llist (tailHeapauxHeap pointerStructfin p heap)
                                                   (tailHeapauxPointer pointerStructfin p heap))
tailFromProgaux B {w} heap nothing = nothing



tailFromProg : (B : Set){w : World}(heapWithPoin : HeapWithPointer B {w})
                   → Maybe (HeapWithPointer B {w})
tailFromProg B {w} heapWithPoin  = tailFromProgaux B {w} (heapWithPoin .llheap) (heapWithPoin .llpoint)



tailFromProgCoraux : (B : Set){w : World}(llp : MPointerfin w)(llh : heapObjectLLMod.HeapObjectLL B pointerStructfin w)
                   → tailFromProg B {w} (llist llh llp) ≡ tail B {w} (llist llh llp)
tailFromProgCoraux B {w} (just x) llh = refl
tailFromProgCoraux B {w} nothing llh = refl


tailFromProgCor : (B : Set){w : World}(heapWithPoin : HeapWithPointer B {w})
                   → tailFromProg B {w} heapWithPoin ≡ tail B {w} heapWithPoin
tailFromProgCor B {w} (llist llheap₁ llpoint₁) = tailFromProgCoraux B {w} llpoint₁ llheap₁
