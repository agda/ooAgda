--@PREFIX@heapAsObjectAttemptSeven
{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --allow-unsolved-metas #-}


--
-- NOTE: This file was not used for the paper!
--
--

module src.heap.heapAsObjectExample where


open import Function using (id; case_of_)


open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)

open import Data.Product using (_,_) renaming (proj₁ to pr₁; proj₂ to pr₂; _×_ to _×'_)

open import Size using (Size; ∞)
open import Data.Sum using (_⊎_; inj₁; inj₂)


open import src.SizedIO.Base using (IOInterface; Command; Response)
open import src.StateSizedIO.RObject using (RInterfaceˢ; Stateˢ; Methodˢ; RMethodˢ; Resultˢ; RResultˢ; nextˢ; RObjectˢ; IOInterfaceˢ; objectMethod; readerMethod; IOStateˢ; Commandˢ; Responseˢ; IOnextˢ; IOˢ';  IOˢ; doˢ'; returnˢ'; forceˢ)

open import src.NativeIO using (String; Unit; unit; NativeIO; _native>>=_; nativeReturn; nativePutStrLn)


open import src.StateSizedIO.writingOOsUsingIOVers4ReaderMethods hiding (nˢ)

open import src.SizedIO.Console using (putStrLn; getLine; consoleI; translateIOConsoleLocal)


--
-- Heap Imports
--
open import src.heap.worldModule

open import src.heap.heapAsObjectBase using (World; sucw; WorldPred; El; lift; ∅w)
open import src.heap.heapAsObjectGeneric using (PointerStruct; Pointer; embedp; pointerStructfin; StoreFin; MPointerfin; ∅Hfin; Pointerfin; newfin; newHfin; writeHfin; ↑)

open import src.heap.heapAsObjectNativeHeap

open import src.heap.heapAsObject







module SimpleHeapProg (pointersimStruct : PointerStruct)             where
    Pointersim : World → Set
    Pointersim = Pointer pointersimStruct


    embedsim  : {w : World} → Pointersim w → Pointersim (sucw w)
    embedsim = embedp pointersimStruct

    wpString : WorldPred
    wpString = constWp (Maybe String)


    simpleHeapProgram : (i : Size) →
                        IOˢindcoind+
                           ConsoleInterfaceˢ
                           (HeapInterfaceˢIO Pointersim wpString)
                           i (λ x y → Unit) unit ∅w

    simpleHeapProgram i = doˢIO (putStrLn "welcome to the heap program!") λ _ →
                          doˢobj∞ (newP nothing) λ p1 →
                          doˢobj (newP (just "time")) λ p2 →
                          doˢobj (newP nothing) λ p3 →
                          doˢobj (newP (just "come.")) λ p4 →
                          doˢobj (writeP (embedsim (embedsim (embedsim p1)))  (just "The")) λ _ →
                          doˢIO (putStrLn "Wrote to heap the words of 'The time has come.'") λ _ →
                          doˢIO∞ (putStrLn "write the number of the heap element you want to print.") λ _ →
                          doˢIO∞ getLine λ _ →
                          endIO∞




open SimpleHeapProg

open heapRObjectFinM -- (wpString pointerStructfin)


mainSimpleHeapProgram : NativeIO Unit
mainSimpleHeapProgram = run+ simpleHeapProgram pointerStructfin ∞ startingWith heapRObject (wpString pointerStructfin) ∅Hfin


mainTranslatedViaAgdaHeap : NativeIO Unit
mainTranslatedViaAgdaHeap = mainSimpleHeapProgram






PointerIORefString : World → Set
PointerIORefString = λ _ → IORef (Maybe String)

embedIORefString : {w : World}(p : PointerIORefString w) → PointerIORefString (sucw w)
embedIORefString = id

iorefStructString : PointerStruct
iorefStructString .Pointer = PointerIORefString
iorefStructString .embedp {w} = embedIORefString{w}





HeapInterIORefˢString : IOInterfaceˢ
HeapInterIORefˢString =  HeapInterfaceˢIO (iorefStructString .Pointer) (wpString iorefStructString)


simpleHeapProgramTranslated : (i : Size) →
                           IOˢ (consoleI ⊎IOIˢhalf  HeapInterIORefˢString) i (λ _ → Unit) ∅w
simpleHeapProgramTranslated i = ioIndCoindToIOˢhalf'+ consoleI HeapInterIORefˢString  (simpleHeapProgram iorefStructString i)



translateNativeIO : IOˢ (consoleI ⊎IOIˢhalf  HeapInterIORefˢString) ∞ (λ _ → Unit) ∅w -> NativeIO Unit
translateNativeIO = translateIOˢ (translateConsoleHeapIORefNativeˢ (constWp (Maybe String)))

mainTranslatedViaNativeHeap : NativeIO Unit
mainTranslatedViaNativeHeap = (nativePutStrLn "This uses the NativeHeap!") native>>= λ _ →
                               translateNativeIO (simpleHeapProgramTranslated  ∞)

main = mainTranslatedViaNativeHeap
