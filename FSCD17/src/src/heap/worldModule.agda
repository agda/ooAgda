{-# OPTIONS --postfix-projections #-}


module src.heap.worldModule where


open import Data.Bool.Base using (T)
open import Data.Empty using (⊥)

open import Data.Maybe.Base using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Nat.Base using () renaming (_⊔_ to _⊔n_)
open import Data.Product using (_,_) renaming (proj₁ to pr₁; proj₂ to pr₂; _×_ to _×'_; map to mapp)
open import Data.Unit using (⊤; tt)

open import src.heap.libraryNat
open import src.heap.libraryFin

open import src.StateSizedIO.Object using (Interfaceˢ; Stateˢ; Methodˢ; Resultˢ; Objectˢ; nextˢ) renaming (objectMethod to method)


--
-- Heap Imports
--
open import src.heap.heapAsObjectBase




module HeapObjectImplementation (wp : WorldPred) where

  HeapStateˢ : Set
  HeapStateˢ = World


  data HeapMethodˢ : (w : HeapStateˢ) → Set where

    -- (El p (sucw w)
    -- this could perhaps benefit from embedding the value )
    newPointer : {w : HeapStateˢ} → wp .El (sucw w) → HeapMethodˢ w

    write      : {w : HeapStateˢ}

                 {w' : HeapStateˢ} {w'w : T (w' ≦w w)} →
                 {w'' : HeapStateˢ} → {w''w : T (w'' ≦w w)} →
                 Pointer w'  → wp .El w'' → HeapMethodˢ w

    writeSimple : {w : HeapStateˢ} → Pointer w → wp .El w → HeapMethodˢ w

    read       : {w : HeapStateˢ}
                 {w' : HeapStateˢ} {w'w : T (w' ≦w w)} → Pointer w' → HeapMethodˢ w

    readSimple : {w : HeapStateˢ}→ Pointer w → HeapMethodˢ w



    getHeap : {w : HeapStateˢ} →  HeapMethodˢ w


  HeapResultˢ : (w : HeapStateˢ) → (m : HeapMethodˢ w ) → Set
  HeapResultˢ w (newPointer _) = Pointer (sucw w)
  HeapResultˢ w (write {w'} {w'w} p x) = ⊤
  HeapResultˢ w (writeSimple p x) = ⊤
  HeapResultˢ w (read {w'} {w'w} p) =  wp .El w
  HeapResultˢ w (readSimple p) =  wp .El w
  HeapResultˢ w getHeap = Heap wp w


  nˢ : (w : HeapStateˢ) (m : HeapMethodˢ w) →
       HeapResultˢ w m → HeapStateˢ
  nˢ w  (newPointer _) _ = sucw w
  nˢ w  _ _ = w



  HeapInterfaceˢ : Interfaceˢ
  HeapInterfaceˢ .Stateˢ           = HeapStateˢ
  HeapInterfaceˢ .Methodˢ hstate   = HeapMethodˢ hstate
  HeapInterfaceˢ .Resultˢ hstate   = HeapResultˢ hstate
  HeapInterfaceˢ .nextˢ   hstate m = nˢ hstate m




  heapObject : ∀{w : World} → (h : Heap wp w) → Objectˢ HeapInterfaceˢ w


  heapObject {w} h .method  (newPointer x) = new , heapObject{sucw w}
                                                       (newH{wp}{w} h x)

  heapObject {w} h .method  (write {_}{w'} {w'w} {w''} {w''w}
                                         p x) = tt , heapObject{w}

                                                   (writeH+{wp}{w} h {w'}{w'w} p

                                                   (lift+ wp w'' w w''w x))

  heapObject {w} h .method  (writeSimple p x) = tt , heapObject{w} (writeH h p x)


  heapObject {w} h .method (read {_} {w'} {w'w} p) = ↑+ {wp}{w} h {w'}{w'w} p , heapObject h

  heapObject {w} h .method (readSimple p) = ↑ {wp}{w} h p , heapObject h


  -- this is for debugging only, will be deleted later!
  heapObject {w} h .method getHeap =  h , heapObject h

  HeapObject = Objectˢ HeapInterfaceˢ



module worldModule (heapElements : World → Set)

                   -- heapElements w is the type of elements pointed
                   --    to on the heap, if they are non-null
                   -- the elements will change because they refer
                   --   to the set of Pointers
                   -- the heap for world w is a function
                   --    Pointer w → heapElements w
                   (liftHeapElements : (w : World) → heapElements w → heapElements (sucw w))
                   --  lifts an element pointed to by the heap froom
                   --  one world to the next world

                   (_==heapElements_ : {w w' : World} → heapElements w → heapElements w' → Set)
                   --  equality for elements on the heap which is
                   --    heterogeneous in the worlds
                   (newType : (w : World) → Set)
                   (new     : {w : World} → newType w → heapElements w)
                   where

  -- heapMElements are the maybe heap elements, which is the type
  --    where pointers point to on the heap
  heapMElements : World → Set
  heapMElements w = Maybe (heapElements w)

  liftHeapMElements : (w : World) → heapMElements w
                                  → heapMElements (sucw w)
  liftHeapMElements w = mapMaybe (liftHeapElements w)

  liftHeapElements+ : ( w w' : World) → T (w ≦w w') →
                    heapElements w → heapElements w'
  liftHeapElements+ w w' ww' a = leqEmbedLem heapElements liftHeapElements
                                 w w' ww' a

  liftHeapMElements+ : ( w w' : World) → T (w ≦w w') →
                    heapMElements w → heapMElements w'
  liftHeapMElements+ w w' ww' a = leqEmbedLem heapMElements liftHeapMElements
                                 w w' ww' a

  objWorldPred : WorldPred
  objWorldPred .El = heapMElements
  objWorldPred .lift = liftHeapMElements



  -- a canonical equality between elements on the heap
  --
  _==Object_ : {w w' : World} → El objWorldPred w  → El objWorldPred w'
                → Set
  _==Object_ {w} {w'} (just a) (just b) = let aa : heapElements (w ⊔n w')
                                              aa = liftHeapElements+ w (w ⊔n w') (⊔isMaxl {w} {w'}) a
                                              bb : heapElements (w ⊔n w')
                                              bb = liftHeapElements+ w' (w ⊔n w') (⊔isMaxr {w} {w'}) b
                                          in aa ==heapElements bb

  _==Object_ {w} {w'} nothing nothing = ⊤
  _==Object_ {w} {w'} _ _ = ⊥

  newM  : {w : World} → newType w → heapMElements w
  newM {w} a = just (new {w} a)


  newNullObject : {w : World}
            (h : Heap objWorldPred w)
            → Heap objWorldPred (sucw w)
  newNullObject h = newH h nothing


  -- writeObject takes a heap for world w and
  -- creates a heap for the same world w
  -- in which at pointer q the element of heapElements is written.
  writeObject : {w : World}
                → (h : Heap (objWorldPred) w)
                → (q : Pointer w)
                → heapMElements w
                → Heap (objWorldPred) w
  writeObject {w} h q o  = writeH h q o


  writeNewObject : {w : World}
                → (h : Heap (objWorldPred) w)
                → (q : Pointer w)
                → newType w
                → Heap (objWorldPred) w
  writeNewObject {w} h q a = writeObject {w} h q (newM {w} a)


  -- writeObject+ is like writeObject, but the pointer and
  -- the element written come from earlier (or the same) worlds
  writeObject+ : {w w' : World}
                → {w'w : T (w' ≦w w)} → (p : Pointer w')
                → (h : Heap objWorldPred w)
                → {w'' : World} → {w''w : T (w'' ≦w w)}
                → heapMElements w''
                → Heap objWorldPred w
  writeObject+ {w} {w'} {w'w} p h {w''} {w''w} o =
                writeObject h (embed+ w' p w w'w) ((lift+ objWorldPred w'' w w''w) o)

  iηh_setO_:=_ : {w w' : World}
                   → {w'w : T (w' ≦w w)}
                   → {w'' : World} → {w''w : T (w'' ≦w w)}
                   → (h : Heap (objWorldPred) w)
                   → (q : Pointer w')
                   → (b : heapMElements w'')
                   → Heap (objWorldPred) w
  iηh_setO_:=_ {w}{w'}{w'w}{w''}{w''w}  h q b
           = writeObject+ {w}{w'}{w'w} q h {w''} {w''w} b

  open HeapObjectImplementation objWorldPred

  record Time : Set where
    field
      world : World
      heap  : HeapObject world
      point : {x : T (1 ≦w world)} → Pointer world

  open Time public

  next : (t : Time)
         → Methodˢ HeapInterfaceˢ (world t)
         → Time
  next t m .world = HeapInterfaceˢ .nextˢ (world t) m  (pr₁ (heap t .method m))
  next t m .heap = pr₂ (heap t .method m)
  next t (newPointer x) .point = pr₁ (heap t .method (newPointer x))

  next t (write  {w}  {w'} {w'w}  {_}{_}
                 poi _) .point = embed+ w' poi w w'w
  next t (writeSimple poi _) .point = poi


  next t (read  {w} {w'} {w'w}
          poi) .point = embed+ w' poi w w'w

  next t (readSimple  {w}
          poi) .point = poi


  next t (getHeap {w}) .point {notzero} = createFinn {w} notzero

  nextResult : (t : Time)
              → (m : Methodˢ HeapInterfaceˢ (world t))
              → Resultˢ HeapInterfaceˢ (world t) m
  nextResult t m = pr₁ (heap t .method  m)

  ∅t : Time
  ∅t .world = ∅w
  ∅t .heap = heapObject ∅H
  ∅t .point {}
