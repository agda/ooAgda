


{-# OPTIONS --postfix-projections #-}


module src.heap.heapAsObjectNativeHeap where

open import Data.Maybe using (Maybe; nothing; just)
open import Size using (Size; ∞)

open import src.SizedIO.Base

open import src.NativeIO



{-# FOREIGN GHC import qualified Data.IORef as IORef #-}

postulate  IORef : Set → Set
{-# COMPILE GHC IORef = type IORef.IORef #-}




postulate
  nativeNewIORef : {A : Set} → A → NativeIO (IORef A)
  nativeReadIORef : {A : Set} → IORef A → NativeIO A
  nativeWriteIORef : {A : Set} → IORef A → A → NativeIO Unit

{-# COMPILE GHC nativeNewIORef = (\ _ -> IORef.newIORef ) #-}
{-# COMPILE GHC nativeReadIORef = (\ _ -> IORef.readIORef ) #-}
{-# COMPILE GHC nativeWriteIORef = (\ _ -> IORef.writeIORef ) #-}



data HeapCommand (A : Set) : Set where
    newIORef : A → HeapCommand A
    readIORef : IORef A → HeapCommand A
    writeIORef : IORef A → A → HeapCommand A
    heapPutStrLn : String → HeapCommand A


HeapResult : {A : Set}(c : HeapCommand A) → Set
HeapResult {A} (newIORef _    ) = IORef A
HeapResult {A} (readIORef _   ) = A
HeapResult {A} (writeIORef _ _) = Unit
HeapResult {A} (heapPutStrLn _) = Unit

HeapInterface : (A : Set) → IOInterface
HeapInterface A .Command  = HeapCommand A
HeapInterface A .Response = HeapResult {A}

translateHeapLocate : {A : Set} (c : HeapCommand A) → NativeIO (HeapResult c)
translateHeapLocate {A} (newIORef a)        = nativeNewIORef a
translateHeapLocate {A} (readIORef mvar)    = nativeReadIORef {A} mvar
translateHeapLocate {A} (writeIORef mvar a) = nativeWriteIORef {A} mvar a
translateHeapLocate {A} (heapPutStrLn str)  = nativePutStrLn str

IOHeap : ∀{i} → {A : Set}(B : Set) → Set
IOHeap {i} {A} B = IO (HeapInterface A) i B

IOHeap' : ∀{i} → {A : Set}(B : Set) → Set
IOHeap' {i} {A} B = IO' (HeapInterface A) i B

translateHeap : {A : Set}{B : Set} → IOHeap {∞} {A} B → NativeIO B
translateHeap = translateIO translateHeapLocate


prog : IOHeap {∞} {Maybe String} Unit
prog .force = do' (newIORef (nothing)) λ mvar →
              do (writeIORef mvar (just "hello")) λ _ →
              do (readIORef mvar) λ { (just str) →
              do (heapPutStrLn str) λ _ →
              return _;

              nothing →
              do (heapPutStrLn "got nothing") λ _ →
              return _ }
