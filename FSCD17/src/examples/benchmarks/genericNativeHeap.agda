
{-# OPTIONS --postfix-projections #-}


module examples.benchmarks.genericNativeHeap where
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




module genericNativeImpl (nativeRepEl : Set)
                         (Type : (A : Set) → Set)
                         (constr : Type (IORef nativeRepEl) → nativeRepEl)
                         (unfold : nativeRepEl → Type (IORef nativeRepEl)) where

  PointerGen : (w : World) → Set
  PointerGen w = IORef nativeRepEl

  iorefPointerStructGen : PointerStruct
  iorefPointerStructGen  .Pointer = PointerGen
  iorefPointerStructGen  .embedp a = a


  WPgen : WorldPred
  WPgen .El w = Type (PointerGen w)
  WPgen .lift w x = x

  heapInter : IOInterfaceˢ
  heapInter = HeapInterfaceˢIO PointerGen WPgen

  transMethod : (w : World) (m : HeapMethodˢ PointerGen WPgen w)
                → NativeIO (HeapResultˢ PointerGen WPgen w m)
  transMethod w (newPh x) =  nativeNewIORef (constr x)
  transMethod w (writePh p x) = nativeWriteIORef p (constr x)

  transRMethod : (w : World) (m : HeapRMethodˢ PointerGen WPgen w)
                → NativeIO (HeapRResultˢ PointerGen WPgen w m)
  transRMethod w (readPh ioref) =
            nativeReadIORef ioref native>>= λ x →
            nativeReturn ( unfold x )


  {-# NON_TERMINATING #-}
  mutual
    translate2NativeGen : {w : World}
                              (p : IOˢindcoind ConsoleInterfaceˢ heapInter ∞ (λ _ _ → Unit) unit w)
                               → NativeIO Unit
    translate2NativeGen {w} p =
              translate2NativeGen+ {w} (p .forceIC)

    translate2NativeGen+ : {w : World}
                               (p : IOˢindcoind+ ConsoleInterfaceˢ heapInter ∞ (λ _ _ → Unit) unit w)
                               → NativeIO Unit
    translate2NativeGen+ {w} (doˢIO c f) =
             translateIOConsoleLocal c native>>= λ r →
             translate2NativeGen {w} (f r)
    translate2NativeGen+ {w} (doˢobj (inj₁ m) f) =
             transMethod w m native>>= λ r →
             translate2NativeGen+ (f r)
    translate2NativeGen+ {w} (doˢobj (inj₂ m) f) =
             transRMethod w m native>>= λ r →
             translate2NativeGen+ (f r)
    translate2NativeGen+ {w} (returnˢic a) =
             nativeReturn a
