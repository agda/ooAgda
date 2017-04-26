


{-# OPTIONS --postfix-projections #-}


module src.heap.heapAsObjectNativeHeap where

open import Data.Maybe using (Maybe; nothing; just)
open import Size using (Size; ∞)

open import SizedIO.Base

open import NativeIO



{- Idea:

    We can write an IO language corresponding to the langauge of
   Mvars
    MVar would be postulated
   but we have commands
     newMVar {A}  depending on A returntype MVar A
     takeMVAr {A}  depending on MVar A returntype A
     putMVar {A} depending on MVar A and A and returntype Unit

   now we can write IO programs referring to MVars and use this
     to create Strings on the heap


   When defining LInked list we have the problem that we would need

    MVar(String x Maybe (MVar (String x Maybe ( ....)))

   anfinite type.

   In Java this is done by having
    X = MVar(String x Maybe (pointer to X)

   unclear how to do it with Mvars
   SOLUTION:
     https://www.schoolofhaskell.com/user/edwardk/unlifted-structures

     data DLL = DLL (IORef (Maybe DLL)) (IORef (Maybe DLL))
   so we would write

     data LL = LL (MVar (String x Maybe LL))



 These IO programs can be translated in Agda into programs operating on
our heap.
   newMVar {A} would use the new function for the Agda heap
   takeMVar {A} would look up the element on the Agda heap
   putMVar  {A} would update the AGda heap

-}





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

{-
nativeNewIORef : {A : Set} (a : A) → NativeIO (IORef A)
nativeNewIORef {A} = nativeNewIORef' {Maybe A}

nativeReadIORef : {A : Set} (p : IORef (Maybe A)) → NativeIO (Maybe A)
nativeReadIORef {A} = anativeReadIORef' {Maybe A}

nativeWriteIORef : IORef (Maybe String) → Maybe String → NativeIO Unit
nativeWriteIORef =  nativeWriteIORef' {Maybe String}
-}


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
