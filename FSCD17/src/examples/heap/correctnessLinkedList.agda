--@PREFIX@correctnessLinkedList
{-# OPTIONS --postfix-projections #-}



module examples.heap.correctnessLinkedList where


open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Maybe using (Maybe; just; nothing)


open import src.heap.heapAsObjectBase using (World; sucw; WorldPred; El; lift; ∅w)
open import src.heap.heapAsObjectGeneric using (PointerStruct; Pointer; embedp; pointerStructfin; StoreFin; MPointerfin; ∅Hfin; Pointerfin)
open import src.heap.worldModule


open import Data.Product using () renaming (proj₁ to pr₁; proj₂ to pr₂; _×_ to _×'_; map to mapp)
open import Data.Unit using (⊤; tt)



open import src.StateSizedIO.RObject using (RObjectˢ; readerMethod) renaming (objectMethod to method)



open import src.heap.heapAsObject hiding (readP;writeP) -- using (HeapRInterfaceˢ; newPh; readPh; writePh) --





{- This file shows the following:
   * It defines Linked slist
   * It defines CorrLinkedList meaning the heap
         is correct
   * It defines IsListll meaning that the linked list corresponds
     to a list
   * it defines l =ll l'  meaning l l' correspond to the same list
   * it defines nil, cons tail on LinkedLists
   * it shows that
         nil cons tail preserve   CorrLinkedList
   * it shows that
         nil cons tail preserve   IsListll
   * it shows that
       head nil = nothing
       tail nil = nothing
       head (cons n s) = n
       tail (cons n s) = s
     provided we were using lists which fulfil CorrLinkedList and
      IsListll
    where in the last case the equality holds w.r.t. representing the same
    list  =ll

    Waht is missing (but probably easy to prove) is that
     cons and tail preserve =ll
    which should follow since we already ahve that
     if ll represents l
    then cons n ll represens (n :: l)
    so if ll =ll ll' then cons n ll =ll cons n ll' via (n :: l)

    and if l represents [] then pop l = nothing
   and  if l repsents (x :: xs) then pop l represents xs
    from which preservation of =ll under pop should follow
-}



module _ (B : Set) (pointStruct : PointerStruct)
                   (let Pointer = Pointer pointStruct)
                   (let embedp   = embedp pointStruct) where

  membedp : {w : World} → Maybe (Pointer w) → Maybe (Pointer (sucw w))
  membedp (just p) = just (embedp p)
  membedp nothing = nothing

--\correctnessLinkedList
--@BEGIN@LinkedListNodeType
  record LinkedListNodeType (w : World) :  Set where --@HIDE-BEG
    constructor linkedListNode
    field
--@HIDE-END
      getElemLL : B
      getNextLL : Maybe (Pointer w)
--@END

  open LinkedListNodeType public

  MLinkedListNodeType : (w : World) → Set
  MLinkedListNodeType w = Maybe (LinkedListNodeType w)

  liftLL : {w : World} (l : LinkedListNodeType w) → LinkedListNodeType (sucw w)
  liftLL l .getElemLL = l .getElemLL
  liftLL l .getNextLL = membedp (l .getNextLL)

  liftMLL : {w : World} (l : MLinkedListNodeType w) → MLinkedListNodeType (sucw w)
  liftMLL {w} (just p) = just (liftLL {w} p)
  liftMLL {w} nothing = nothing

--\correctnessLinkedList
--@BEGIN@glinkedWP
  gLinkedWP : WorldPred
  gLinkedWP .El = LinkedListNodeType
  gLinkedWP .lift w = liftLL {w}
--@END



module heapObjectLLMod (B : Set) (pointStruct : PointerStruct)

  -- Type of pointers
  (let Pointer = Pointer pointStruct)

  (let embedp = embedp pointStruct)
  (let HeapElWP = gLinkedWP B pointStruct)

  -- Type of heap elements (cons cells in this case).
  (let HeapEl = HeapElWP .El) where




   -- The heap (stores linked lists).

   HeapObjectLL : World → Set
   HeapObjectLL =  RObjectˢ (HeapRInterfaceˢ Pointer HeapElWP)

   -- Heap after allocation of a new cell.

   nextH : {w : World} → HeapEl (sucw w)
                       → HeapObjectLL w
                       → HeapObjectLL (sucw w)
   nextH newPoint h = pr₂ (h .method (newPh newPoint))

   -- Pointer to the new cell.

   newH : {w : World} → HeapEl (sucw w)
                       → HeapObjectLL w
                       → Pointer (sucw w)
   newH newPoint h = pr₁ (h .method (newPh newPoint))

   -- Reading a cell from the heap.

   readP : {w : World} → HeapObjectLL w → Pointer w → HeapEl w
   readP h p = h .readerMethod (readPh p)

   -- Reading a pointer (which can be null).

   mreadP : {w : World} → HeapObjectLL w → Maybe (Pointer w) → Maybe (HeapEl w)
   mreadP h (just p) = just (h .readerMethod (readPh p))
   mreadP h nothing = nothing

   -- Writing to a pointer.

   writeP : {w : World} → HeapObjectLL w → Pointer w → HeapEl w
            → HeapObjectLL w
   writeP h p mo = pr₂ (h .method (writePh p mo))


open heapRObjectFinM  -- Model implementation of heaps where pointers are Fin.

module moduleHeapDef (B : Set)
         (let HeapElWP = gLinkedWP B pointerStructfin)
         (let HeapEl = HeapElWP .El)
         where
  open heapObjectLLMod B pointerStructfin

  -- A heap managing object is canonical if it is created by the heapRObject constructor.
  -- The following predicate expresses that a heap managing object is canonical.

  record HeapCorrect {w : World}(h : HeapObjectLL w) : Set where
    field
      -- The store for the heap.
      theStoreFin  : StoreFin HeapElWP w
      -- Canonicity property.
      eqToStoreFin : h ≡ heapRObject HeapElWP theStoreFin
  open HeapCorrect public

  -- The canonical heap manager is trivially correct.

  corHeapObjectLL : {w : World} → (st : StoreFin HeapElWP w) → HeapCorrect (heapRObject HeapElWP st)
  corHeapObjectLL {w} st .HeapCorrect.theStoreFin  = st
  corHeapObjectLL {w} st .HeapCorrect.eqToStoreFin = refl







  -- Closure of a pointer (bundling a pointer with the heap it refers to).
  -- Pointer may be null.

  record HeapWithPointer {w : World} : Set where
     constructor llist
     field
        llheap    : HeapObjectLL w
        llpoint   : MPointerfin w

  open HeapWithPointer public

  -- A closure is correct if its heap is.

  CorrHeapWithPointer : {w : World} → HeapWithPointer {w} → Set
  CorrHeapWithPointer {w} l  = HeapCorrect (l .llheap)



  CorrMaybeHeapWithPointer : {w : World} → Maybe (HeapWithPointer {w}) → Set
  CorrMaybeHeapWithPointer nothing = ⊤
  CorrMaybeHeapWithPointer (just l) = CorrHeapWithPointer l

  -- Nil: empty linked list.
  -- Represented as the null pointer in the empty heap.

  nill : HeapWithPointer {∅w}
  nill .llheap = heapRObject HeapElWP ∅Hfin
  nill .llpoint = nothing

  -- Nil is correct.

  corNill : CorrHeapWithPointer nill
  corNill = corHeapObjectLL ∅Hfin -- (newNullObject ∅H)


  tailaux : {w : World} → HeapObjectLL w → Maybe (HeapEl w) → Maybe (HeapWithPointer {w})
  tailaux h (just x) = just (llist h (x .getNextLL))
  tailaux h nothing = nothing

  -- Reading the tail of a linked list.  Might be undefined.

  tail : {w : World} → HeapWithPointer {w} → Maybe (HeapWithPointer {w})
  tail l = tailaux (l .llheap) (mreadP (l .llheap) (l .llpoint))



  corTail' : {w : World} {h : HeapObjectLL w}
             → HeapCorrect h
             → (p : Maybe (HeapEl w))
             → CorrMaybeHeapWithPointer {w} (tailaux h p)
  corTail' cor (just x) = cor
  corTail' cor nothing = tt

  -- Correctness proof of the tail function.
  -- (Trivial as heap does not change)

  corTail : {w : World} → (l : HeapWithPointer {w})
            → CorrHeapWithPointer {w} l
            → CorrMaybeHeapWithPointer {w} (tail l)
  corTail l cor = corTail' cor (mreadP (l .llheap) (l .llpoint))

  tail' : {w : World} → (h : HeapObjectLL w) → (p : MPointerfin w)
          → Maybe (HeapWithPointer {w})
  tail' h p = tailaux h (mreadP h p)



  headaux : {w : World} → Maybe (HeapEl w) → Maybe B
  headaux (just x) = just (x .getElemLL)
  headaux nothing = nothing

  head : {w : World} → HeapWithPointer {w} → Maybe B
  head l = headaux (mreadP (l .llheap) (l .llpoint))


  lemmaNilTail : tail nill ≡ nothing
  lemmaNilTail = refl
  lemmaNilHead : head nill ≡ nothing
  lemmaNilHead = refl


  consLLForHeadUnpack : {w : World} → B
                      → MPointerfin w
                      → HeapEl (sucw w)
  consLLForHeadUnpack {w} n p = linkedListNode n (membedp B pointerStructfin p)

  consStoreFinUnpack : {w : World} → B
                      → StoreFin HeapElWP  w
                      → MPointerfin w
                      → HeapObjectLL (sucw w)
  consStoreFinUnpack {w} b h p = nextH (consLLForHeadUnpack b p) (heapRObject HeapElWP h)


  consHeapUnpack : {w : World} → B
                      → HeapObjectLL w
                      → MPointerfin w
                      → HeapObjectLL (sucw w)
  consHeapUnpack n h p = nextH (consLLForHeadUnpack n p) h

  consNewStoreFinUnpack : {w : World} → B
                      → StoreFin HeapElWP  w
                      → MPointerfin w
                      → Pointerfin (sucw w)
  consNewStoreFinUnpack {w} b h p = newH (consLLForHeadUnpack b p) (heapRObject HeapElWP h)


  consNewUnpack : {w : World} → B
                        → HeapObjectLL w
                        → MPointerfin w
                        → Pointerfin (sucw w)
  consNewUnpack n h p = newH (consLLForHeadUnpack n p) h


  consLLForHead : {w : World} → B → HeapWithPointer {w} → HeapEl (sucw w)
  consLLForHead {w} n l = linkedListNode n (membedp B pointerStructfin (l .llpoint))

  consHeap : {w : World} → B → HeapWithPointer {w} → HeapObjectLL (sucw w)
  consHeap n l = nextH (consLLForHead n l) (l .llheap)

  consNew : {w : World} → B → HeapWithPointer {w} → Pointerfin (sucw w)
  consNew n l = newH (consLLForHead n l) (l .llheap)

  cons : {w : World} → B → HeapWithPointer {w} → HeapWithPointer {sucw w}
  cons {w} n l .llheap = consHeap n l
  cons {w} n l .llpoint = just (consNew n l)
