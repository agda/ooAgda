--@PREFIX@heapAsObjectGeneric@
{-# OPTIONS --postfix-projections #-}
open import Data.Nat hiding (_≟_) renaming (_⊔_ to _⊔n_)


module src.heap.heapAsObjectGeneric  where


open import Data.Fin using (Fin; suc; zero)
open import Data.Maybe using (Maybe; just; nothing)


--
-- Heap Imports:
--

open import src.heap.heapAsObjectBase using (World; sucw; WorldPred; El; liftWorldPred; lift; ∅w)




--heapAsObjectGeneric
--@BEGIN@PointerStruct
record PointerStruct : Set₁ where --@HIDE-BEG
  field
--@HIDE-END
    Pointer  :  (w : World)  → Set
    embedp   :  {w : World}  (p : Pointer w) → Pointer (sucw w)
--@END


open PointerStruct public

--heapAsObjectGeneric
--@BEGIN@PointerFin
Pointerfin : World → Set
Pointerfin = Fin

embedfin : {w : World}(p : Pointerfin w) → Pointerfin (sucw w)
embedfin p = suc p

newfin : {w : World} → Pointerfin (sucw w)
newfin = zero

pointerStructfin : PointerStruct
--@END

MPointerfin : World → Set
MPointerfin w = Maybe (Pointerfin w)


pointerStructfin .Pointer = Pointerfin
pointerStructfin .embedp = embedfin

{-# INLINE pointerStructfin #-}


--@BEGIN@Storeg
record Storeg (ptrStruct : PointerStruct) (wp : WorldPred)  (w : World) : Set where  --@HIDE-BEG
   field
--@HIDE-END
       ↑ : ptrStruct .Pointer w → wp .El w
--@END
open Storeg public

--heapAsObjectGeneric
--@BEGIN@liftStoreg
liftStoreg : ∀ (ptrStruct : PointerStruct) {wp : WorldPred} {w : World}
           → Storeg ptrStruct wp (suc w)
           → Storeg ptrStruct (liftWorldPred wp) w
↑ (liftStoreg ptrStruct {wp} {w} h) p = ↑ h (ptrStruct .embedp  p)
--@END


-- we replace HeapFin by StoreFin

--heapAsObjectGeneric
--@BEGIN@StoreFin
StoreFin : (wp : WorldPred) → World → Set
StoreFin wp w = Storeg pointerStructfin wp w
--@END

--heapAsObjectGeneric
--@BEGIN@liftStoreFin
liftStoreFin : ∀ {wp w} → StoreFin wp (suc w) → StoreFin (liftWorldPred wp) w
↑ (liftStoreFin h) p = ↑ h (suc p)
--@END

--heapAsObjectGeneric
--@BEGIN@newStoreFin@newHfin
newHfin : ∀ {wp w} → StoreFin wp w → wp .El (sucw w) → StoreFin wp (sucw w)
↑ (newHfin           h a) zero     =  a
↑ (newHfin {wp} {w}  h a) (suc x)  =  lift wp w (↑ h x)
--@END

--heapAsObjectGeneric
--@BEGIN@writeHfin
writeHfin : ∀ {wp w} → StoreFin wp w → Pointerfin w →  wp .El w → StoreFin wp w
↑ (writeHfin       h zero     a)  zero     =  a
↑ (writeHfin       h zero     a)  (suc q)  =  ↑ h (suc q)
↑ (writeHfin       h (suc p)  a)  zero     =  ↑ h zero
↑ (writeHfin {wp}  h (suc p)  a)  (suc q)  =  ↑ (writeHfin {liftWorldPred wp} (liftStoreFin h) p a) q
--@END

--heapAsObjectGeneric
--@BEGIN@emptyHfin
∅Hfin : ∀ {wp : WorldPred} → StoreFin wp ∅w
↑ ∅Hfin ()
--@END
