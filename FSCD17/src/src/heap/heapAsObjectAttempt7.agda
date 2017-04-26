--@PREFIX@heapAsObjectAttemptSeven
{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --allow-unsolved-metas #-}

module src.heap.heapAsObjectAttempt7 where
{-

open import Function using (id; case_of_)


open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)

open import Data.Product using (_,_) renaming (proj₁ to pr₁; proj₂ to pr₂; _×_ to _×'_)

open import Size using (Size; ∞)
open import Data.Sum using (_⊎_; inj₁; inj₂)


open import SizedIO.Base using (IOInterface; Command; Response)
open import StateSizedIO.RObject using (RInterfaceˢ; Stateˢ; Methodˢ; RMethodˢ; Resultˢ; RResultˢ; nextˢ; RObjectˢ; IOInterfaceˢ; objectMethod; readerMethod; IOStateˢ; Commandˢ; Responseˢ; IOnextˢ; IOˢ';  IOˢ; doˢ'; returnˢ'; forceˢ)

open import NativeIO using (String; Unit; unit; NativeIO; _native>>=_; nativeReturn; nativePutStrLn)

open import StateSizedIO.writingOOsUsingIOVers4ReaderMethods hiding (nˢ)

open import SizedIO.Console using (putStrLn; getLine)

open import SizedIO.Console using (consoleI; translateIOConsoleLocal)


--
-- Heap Imports:
--
open import src.heap.heapAsObject using (World; sucw; WorldPred; El; lift; ∅w)
open import src.heap.heapAsObjectGeneric using (PointerStruct; Pointer; embedp; pointerStructfin; StoreFin; MPointerfin; ∅Hfin; Pointerfin; newfin; newHfin; writeHfin; ↑)
open import src.heap.worldModule

open import src.heap.heapAsObjectAttempt7NativeHeap



-- World-independent set.

constWp : (A : Set) → WorldPred
constWp A .El _ = A
constWp A .lift w x = x

stringWp : WorldPred
stringWp = constWp (Maybe String)






module HeapGeneric (Pointerg : World → Set) where

{-
  Pointerg = Pointer   pointerstruct
  embedg   = embedp pointerstruct
-}

  module HeapGenericWp  (wp : WorldPred) where
--@C
--@C
    HeapStateˢ : Set
    HeapStateˢ = World
--@C

--@BEGIN@DefHeapGeneric
    data HeapMethodˢ : (w : HeapStateˢ) → Set where
--@C
--@C  -- (El p (sucw w)
--@C  -- this could perhaps benefit from embedding the value )
      newPh    :  {w : HeapStateˢ} (x :  wp .El (sucw w)) → HeapMethodˢ w
--@C
--@C
      writePh  :  {w : HeapStateˢ} (p : Pointerg w) (x : wp .El w) → HeapMethodˢ w
--@C
--@C
--@C

    data HeapRMethodˢ : (w : HeapStateˢ) → Set where
      readPh   :  {w : HeapStateˢ} (p :  Pointerg w) → HeapRMethodˢ w
--@C
--@C
--@C

    HeapResultˢ : (w : HeapStateˢ) (m : HeapMethodˢ w ) → Set
    HeapResultˢ w (newPh _)      =  Pointerg (sucw w)
    HeapResultˢ w (writePh p x)  =  Unit
--@C

    HeapRResultˢ : (w : HeapStateˢ) (m : HeapRMethodˢ w ) → Set
    HeapRResultˢ w (readPh p)  =  wp .El w

    nˢ : (w : HeapStateˢ) (m : HeapMethodˢ w)(r : HeapResultˢ w m) → HeapStateˢ
    nˢ w  (newPh _)  _  =  sucw w
    nˢ w  _          _  =  w
--@END

--@BEGIN@DefHeapGenericInterface
    HeapRInterfaceˢ : RInterfaceˢ
--@END
    HeapRInterfaceˢ .Stateˢ             =  HeapStateˢ
    HeapRInterfaceˢ .Methodˢ  hstate    =  HeapMethodˢ hstate
    HeapRInterfaceˢ .RMethodˢ hstate    =  HeapRMethodˢ hstate
    HeapRInterfaceˢ .Resultˢ  hstate    =  HeapResultˢ hstate
    HeapRInterfaceˢ .RResultˢ hstate    =  HeapRResultˢ hstate
    HeapRInterfaceˢ .nextˢ    hstate m  =  nˢ hstate m

--@BEGIN@DefHeapGenericObject
    HeapObject : HeapRInterfaceˢ .Stateˢ → Set
    HeapObject = RObjectˢ HeapRInterfaceˢ
--@END

--@BEGIN@DefHeapInterfaceIO
    HeapInterfaceˢIO : IOInterfaceˢ
    HeapInterfaceˢIO = objectInterfToIOInterfˢ  HeapRInterfaceˢ
--@END

  open HeapGenericWp public
open HeapGeneric public

{-
  Pointerg = Pointer   pointerstruct
  embedg   = embedp pointerstruct
-}

-- Pretty names for the methods manipulating the heap.

module _ {Pointerg : World → Set}{wp : WorldPred} where

    HeapMethods = λ w → HeapMethodˢ Pointerg wp w ⊎ HeapRMethodˢ Pointerg wp w

    newP  : {w : HeapStateˢ Pointerg wp} → wp .El (sucw w) → HeapMethods w
    newP {w} p = inj₁ (newPh p)

    writeP  : {w : HeapStateˢ Pointerg wp} → Pointerg w → wp .El w → HeapMethods w
    writeP {w} p a = inj₁ (writePh p a)

    readP  : {w : HeapStateˢ Pointerg wp} → Pointerg w → HeapMethods w
    readP {w} p = inj₂ (readPh p)






HeapRInterfaceˢfin : (wp : WorldPred) → RInterfaceˢ
HeapRInterfaceˢfin = HeapRInterfaceˢ Pointerfin


HeapRObjectfin :  (wp : WorldPred)(w : World) → Set
--@BEGIN@HeapRObjectfin
HeapRObjectfin wp = RObjectˢ (HeapRInterfaceˢfin wp )
--@END

module heapRObjectFinM (wp : WorldPred) where

--@BEGIN@HeapRObjectConstr
  heapRObject : ∀{w : World} → (h : StoreFin wp w) → HeapRObjectfin wp w
  heapRObject h .objectMethod (newPh x)      =  newfin , heapRObject (newHfin h x)
  heapRObject h .objectMethod (writePh p x)  =  _ , heapRObject (writeHfin h p x)
  heapRObject h .readerMethod (readPh p)     =  ↑ h p
--@END





open heapRObjectFinM -- (wpString pointerStructfin)

{---
--- WRITE THIS IN NEW FILE ASAP:
---

mainSimpleHeapProgram : NativeIO Unit
mainSimpleHeapProgram = run+ simpleHeapProgram pointerStructfin ∞ startingWith heapRObject (wpString pointerStructfin) ∅Hfin


mainTranslatedViaAgdaHeap : NativeIO Unit
mainTranslatedViaAgdaHeap = mainSimpleHeapProgram


--}



_⊎IOIˢhalf_ : (I : IOInterface) (I' : IOInterfaceˢ) → IOInterfaceˢ
(I ⊎IOIˢhalf I') .IOStateˢ = I' .IOStateˢ
(I ⊎IOIˢhalf I') .Commandˢ s = I .Command ⊎ I' .Commandˢ  s
(I ⊎IOIˢhalf I') .Responseˢ s (inj₁ c) = I .Response c
(I ⊎IOIˢhalf I') .Responseˢ s (inj₂ c) = I' .Responseˢ s c
(I ⊎IOIˢhalf I') .IOnextˢ s (inj₁ c) r = s
(I ⊎IOIˢhalf I') .IOnextˢ s (inj₂ c) r = I' .IOnextˢ s c r



module _ (I₁ : IOInterface )
         (let I₁'' = unsizedIOInterfToIOInterfˢ I₁)
--         (let I₁' = objectInterfToIOInterf I₁)
         (I₂ : IOInterfaceˢ )
         (let S₂ = IOStateˢ I₂)
         (let C₂ = Commandˢ I₂)
         (let R₂ = Responseˢ I₂)
         (let next₂ = IOnextˢ I₂)
           where

  mutual
    ioLeft2IOˢhalfDisjoint' : ∀{i}{A}{s} →  IOˢ' I₁'' i (λ _ → A s) _ → IOˢ' (I₁ ⊎IOIˢhalf I₂) i A s
    ioLeft2IOˢhalfDisjoint' (doˢ' c f) = doˢ' (inj₁ c) λ r →
                                        ioLeft2IOˢhalfDisjoint (f r)
    ioLeft2IOˢhalfDisjoint' (returnˢ' a) = returnˢ' a

    ioLeft2IOˢhalfDisjoint : ∀{i}{A}{s} →  IOˢ I₁'' i (λ _ → A s) _ → IOˢ (I₁ ⊎IOIˢhalf I₂) i A s
    ioLeft2IOˢhalfDisjoint p .forceˢ =  ioLeft2IOˢhalfDisjoint' (p .forceˢ)

  mutual
    ioIndCoindToIOˢhalf  : ∀{i} → {A : S₂ → Set} → {s : S₂}
                             → IOˢindcoind I₁'' I₂ i (λ _ → A) _ s
                             → IOˢ (I₁ ⊎IOIˢhalf I₂) i A s
    ioIndCoindToIOˢhalf {i} {A} {s} p .forceˢ {j} = ioIndCoindToIOˢhalf+  {j}{A} (p .forceIC {j})




    ioIndCoindToIOˢhalf+  : ∀{i} → {A : S₂ → Set}{s : S₂}
                             → IOˢindcoind+ I₁'' I₂ i (λ _ → A) _ s
                             → IOˢ' (I₁ ⊎IOIˢhalf I₂) i A s
    ioIndCoindToIOˢhalf+ {i} {A} (doˢobj c f) = doˢ' (inj₂ c) λ r → ioIndCoindToIOˢhalf'+ (f r)
    ioIndCoindToIOˢhalf+ {i} {A} (doˢIO c f) = doˢ' (inj₁ c) λ r → ioIndCoindToIOˢhalf (f r)
    ioIndCoindToIOˢhalf+ {i} {A} (returnˢic a) = returnˢ' a



    ioIndCoindToIOˢhalf'+  : ∀{i} → {A : S₂ → Set}{s : S₂}
                             → IOˢindcoind+ I₁'' I₂ i (λ _ → A) _ s
                             → IOˢ (I₁ ⊎IOIˢhalf I₂) i A s
    ioIndCoindToIOˢhalf'+ {i} {A} p .forceˢ = ioIndCoindToIOˢhalf+ {i} {A} p


disjointUnionTranslate : (I : IOInterface)
                         (I' : IOInterfaceˢ)
                         (translateI : (c : Command I)   → NativeIO (Response I c))
                         (translateI' : (s : IOStateˢ I')(c : Commandˢ I' s)   → NativeIO (Responseˢ I' s  c))
                         (s : IOStateˢ (I ⊎IOIˢhalf I'))
                         (c : Commandˢ (I ⊎IOIˢhalf I') s)
                         → NativeIO (Responseˢ (I ⊎IOIˢhalf I') s c)
disjointUnionTranslate I I' translateI translateI' s (inj₁ c) = translateI c
disjointUnionTranslate I I' translateI translateI' s (inj₂ c) = translateI' s c











module _ (wp : PointerStruct → WorldPred) where

--@BEGIN@genericHeapProgram
  GenericHeapProgram : (w : World) → Set₁
  GenericHeapProgram w = (pointerStruct : PointerStruct)
                          → IOˢindcoind+  ConsoleInterfaceˢ
                             (HeapInterfaceˢIO (Pointer pointerStruct) (wp pointerStruct)) ∞
                             (λ _ _ → Unit) unit w
--@END

  SizedGenericHeapProgram : Set₁
  SizedGenericHeapProgram   = (pointerStruct : PointerStruct)
                              (i : Size)
                              (w : World)
                              → IOˢindcoind+
                               ConsoleInterfaceˢ
                               (HeapInterfaceˢIO (Pointer pointerStruct) (wp pointerStruct)) i
                               (λ _ _ → Unit) unit w

--@BEGIN@generProgramToNativeIOUsingAgdaHeap
  genProgr2NativeIOUsingAgdaHeap : (w : World) (prog : GenericHeapProgram w)
                                   (obj : RObjectˢ (HeapRInterfaceˢ  Pointerfin
                                                  (wp pointerStructfin))  w)
                                   → NativeIO Unit
  genProgr2NativeIOUsingAgdaHeap w prog obj = run+ (prog pointerStructfin) startingWith obj
--@END

--@BEGIN@compileGenericHeapProgUsingAgdaHeap
  compileGenericHeapProgUsingAgdaHeap :  (prog : GenericHeapProgram ∅w)
                                         → NativeIO Unit
  compileGenericHeapProgUsingAgdaHeap prog =
    run+ (prog pointerStructfin) startingWith heapRObject (wp pointerStructfin) ∅Hfin
--@END


-- ∅Hfin


--
module _ (wp : WorldPred)
         (let HeapInterIORefˢString = HeapInterfaceˢIO (λ w → IORef (wp .El w)) wp)  where

    translateHeapInterIORefLocalˢ : (s : IOStateˢ HeapInterIORefˢString)
          (c : Commandˢ HeapInterIORefˢString s) →
          NativeIO (Responseˢ HeapInterIORefˢString s c)
    translateHeapInterIORefLocalˢ _ (inj₁ (newPh x)) = nativeNewIORef x
    translateHeapInterIORefLocalˢ _ (inj₁ (writePh x x₁)) =  nativeWriteIORef x x₁
    translateHeapInterIORefLocalˢ _ (inj₂ (readPh x)) = nativeReadIORef x



    translateConsoleHeapIORefNativeˢ : (s : ℕ) (c : consoleI .Command ⊎ HeapInterIORefˢString .Commandˢ s)
                                       → NativeIO (Responseˢ (consoleI ⊎IOIˢhalf HeapInterIORefˢString) s c)
    translateConsoleHeapIORefNativeˢ = disjointUnionTranslate
                                              consoleI HeapInterIORefˢString
                                              translateIOConsoleLocal
                                              translateHeapInterIORefLocalˢ

--
-- I use here "translateIOˢ", but could also use
-- use "flattern" to translate it to an non-state dependent
-- interface, that is actually the case (for the NativeHeap programs)
--

module _  {I : IOInterfaceˢ}
                (let S = IOStateˢ I)     (let C  = Commandˢ I)
                (let  R  = Responseˢ I) (let next = IOnextˢ I) where
  {-# NON_TERMINATING #-}

  translateIOˢ : ∀{A : Set }{s : S}
    →  (translateLocal : (s : S) → (c : C s) → NativeIO (R s c))
    →  IOˢ I ∞ (λ _ → A) s
    →  NativeIO A
  translateIOˢ {A} {s} translateLocal p = case (forceˢ p {_}) of
    λ{ (doˢ' c f)    → (translateLocal s c)     native>>= λ r →
                             translateIOˢ translateLocal (f r)
     ; (returnˢ' a) → nativeReturn a
     }
-}
