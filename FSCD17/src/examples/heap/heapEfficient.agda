--@PREFIX@heapEfficient
{-# OPTIONS --postfix-projections #-}

module examples.heap.heapEfficient where


open import Function

open import Size hiding (↑_)
open import Data.Sum

open import src.StateSizedIO.Base

open import src.NativeIO

open import src.heap.heapAsObjectBase  hiding (Pointer)
open import src.heap.heapAsObjectGeneric

open import src.StateSizedIO.writingOOsUsingIOReaderMethods

open import src.SizedIO.Console using (putStrLn; getLine; consoleI; translateIOConsoleLocal)


open import src.heap.heapAsObjectNativeHeap

open import src.heap.heapAsObject

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

{-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}

nativeMaybeFunc : {A : Set} {B : Set} → (A → B) → Maybe A → Maybe B
nativeMaybeFunc f (just x) = just (f x)
nativeMaybeFunc f nothing = nothing


{-# FOREIGN GHC import qualified Data.IORef as IORef #-}

--@BEGIN@FFI
{-# FOREIGN GHC data NativeLL a = LLConstr a (Maybe (IORef.IORef (NativeLL a))) #-}
--@END

{-# FOREIGN GHC
hsNode :: a -> Maybe (IORef.IORef (NativeLL a)) -> NativeLL a
hsNode = LLConstr

getItem :: NativeLL t -> t
getItem (LLConstr x _) = x

getNext :: NativeLL t -> Maybe (IORef.IORef (NativeLL t))
getNext (LLConstr _ next) = next
#-}

--@BEGIN@Postulates
postulate nativeLL : Set → Set
          nativeNodeConstr : {A : Set} → A → Maybe (IORef (nativeLL A)) → nativeLL A
          IORef₋  : Set → Set
--@END
          getItem : {A : Set} → nativeLL A → A
          getNext : {A : Set} → nativeLL A → (Maybe (IORef (nativeLL A)))

{-# COMPILE GHC nativeLL = type NativeLL #-}
{-# COMPILE GHC nativeNodeConstr = (\x -> hsNode) #-}
{-# COMPILE GHC getItem = (\x -> getItem) #-}
{-# COMPILE GHC getNext = (\x -> getNext) #-}


record LinkedListNodeType (A : Set) (w : World) (Point : World → Set) :  Set where
  constructor node
  field getElemLL  : A
        getNextLL  : Maybe (Point w)



PointerIORefLL : {A : Set} → World → Set
PointerIORefLL {A} = λ w → IORef (nativeLL A)

embedIORefLL : {A : Set}{w : World}(p : PointerIORefLL {A} w) → PointerIORefLL {A} (sucw w)
embedIORefLL = λ x → x

iorefStructLL : {A : Set} → PointerStruct
iorefStructLL {A} .Pointer = PointerIORefLL{A}
iorefStructLL {A} .embedp {w} = embedIORefLL{A} {w}


wpBHGen : {A : Set} → (PointerStruct) → WorldPred
wpBHGen {A} (pSt) .El w = LinkedListNodeType A w (pSt .Pointer)
wpBHGen {A} (pSt) .lift w (node item next) = node item (nativeMaybeFunc (pSt .embedp {w}) next)

wpBH : {B : Set} → WorldPred
wpBH {B} = wpBHGen {B} (iorefStructLL{B})




--@BEGIN@iorefStruct
iorefStruct : (A : Set) → PointerStruct
iorefStruct A .Pointer  w  =  IORef (nativeLL A)
iorefStruct A .embedp   p  =  p
--@END

--@BEGIN@INLINE
{-# INLINE iorefStruct #-}
--@END

--@BEGIN@toNativeElement
toNativeElement : {A : Set}{w : World} → LinkedListNodeType A w (iorefStruct A .Pointer) → nativeLL A
toNativeElement {A} (node item next) = nativeNodeConstr item next
--@END

--@BEGIN@iorefWp
iorefWp : (A : Set) → WorldPred
--@END
iorefWp A = wpBHGen {A} (iorefStruct A)

--@BEGIN@iorefHeapInter
iorefHeapInter : (A : Set) → IOInterfaceˢ
iorefHeapInter A = HeapInterfaceˢIO (iorefStruct A .Pointer) (iorefWp A)
--@END


--@BEGIN@ttransMethodBinaryHeap
transMethod : ∀ {A w} (m : HeapMethodˢ (iorefStruct A .Pointer) (iorefWp A) w)
                → NativeIO (HeapResultˢ (iorefStruct A .Pointer) (iorefWp A) w m)
transMethod (newPh (node elem next)) = nativeNewIORef (nativeNodeConstr elem next)
--@END
transMethod (writePh p element) = nativeWriteIORef p (toNativeElement element)



transRMethod : ∀{A w} (m : HeapRMethodˢ (λ w₁ → IORef (nativeLL A)) wpBH w)
                   → NativeIO (HeapRResultˢ (λ w₁ → IORef (nativeLL A)) wpBH w m)
transRMethod (readPh  ioref) = nativeReadIORef ioref native>>= λ llNode →
  nativeReturn (node (getItem llNode) (getNext llNode))


ConsoleCommand : Set
ConsoleCommand = src.SizedIO.Console.ConsoleCommand

ConsoleResponse : src.SizedIO.Console.ConsoleCommand → Set
ConsoleResponse = src.SizedIO.Console.ConsoleResponse

-- @BEGIN@ttranslateIOConsoleNative
translateIOConsoleNative : (c : ConsoleCommand) → NativeIO (ConsoleResponse c)
-- @END
translateIOConsoleNative = translateIOConsoleLocal

{-# NON_TERMINATING #-}
--@BEGIN@translateToNative
translate2Native : {A : Set}(w : World)
                    → IOˢindcoind ConsoleInterfaceˢ (iorefHeapInter A) ∞ (λ _ _ → Unit) unit w
                    → NativeIO Unit
--@END
translate2Native w p = case (forceIC p {_}) of
   λ{ (doˢIO c f) → translateIOConsoleLocal c native>>= λ r → translate2Native w (f r)
   ; (doˢobj (inj₁ c) f) → transMethod c native>>= λ r →
                            translate2Native
                            (HeapGenericWp.nˢ (Pointer iorefStructLL) wpBH w c r)
                            (delayˢic (f r))

   ; (doˢobj (inj₂ c) f) → transRMethod  c native>>= λ r →
                           translate2Native
                               (IOnextˢ (HeapInterfaceˢIO (Pointer iorefStructLL)
                                                          wpBH) w (inj₂ c) r)
                               (delayˢic (f r))

   ; (returnˢic a) →  nativeReturn a
   }




sizedHeapProgramToNativeHeapIO : {A : Set}(w : World)
                                 (prog : SizedGenericHeapProgram wpBHGen)
                                  → NativeIO Unit
sizedHeapProgramToNativeHeapIO {A} w prog = let progSized : GenericHeapProgram wpBHGen w
                                                progSized pointersimStruct = (prog pointersimStruct ∞ w)
                                            in
                                             (nativePutStrLn "This uses the NativeHeap!") native>>= λ _ →
                                             translate2Native{A} w (delayˢic (progSized (iorefStructLL {A} )))
