
{-# OPTIONS --postfix-projections #-}


module examples.benchmarks.nativeBinaryTree where

open import Data.Maybe hiding (map)
open import src.heap.libraryMaybe

open import src.heap.heapAsObjectNativeHeap

open import src.heap.heapAsObject

open import  examples.benchmarks.genericNativeHeap




--
-- Native Heap
--

nativeMaybe2Maybe : {A : Set} → NativeMaybe A → Maybe A
nativeMaybe2Maybe nothingNative = nothing
nativeMaybe2Maybe (justNative x) = just x

maybe2NativeMaybe : {A : Set} → Maybe A → NativeMaybe A
maybe2NativeMaybe (just x) = justNative x
maybe2NativeMaybe nothing = nothingNative



{-# FOREIGN GHC import qualified Data.IORef as IORef #-}

{-# FOREIGN GHC

data LL a = LLConstr ! a ! (Maybe (IORef.IORef (LL a))) ! (Maybe (IORef.IORef (LL a)))

hsNode :: a -> Maybe (IORef.IORef (LL a)) -> Maybe (IORef.IORef (LL a)) -> LL a
hsNode = LLConstr

getItem :: LL t -> t
getItem (LLConstr x _ _) = x

getLeft :: LL t -> Maybe (IORef.IORef (LL t))
getLeft (LLConstr _ l _) = l

getRight :: LL t -> Maybe (IORef.IORef (LL t))
getRight (LLConstr _ _ r) = r
#-}



postulate
  nativeLL : Set → Set
  nativeNodeConstr : {A : Set} → (a : A)(l l' : (NativeMaybe (IORef (nativeLL A)))) → nativeLL A
  getItem : {A : Set} → nativeLL A → A
  getLeft : {A : Set} → nativeLL A → (NativeMaybe (IORef (nativeLL A)))
  getRight : {A : Set} →  nativeLL A → (NativeMaybe (IORef (nativeLL A)))

{-# COMPILE GHC nativeLL = type LL #-}
{-# COMPILE GHC nativeNodeConstr = (\x -> hsNode) #-}
{-# COMPILE GHC getItem = (\x -> getItem) #-}
{-# COMPILE GHC getLeft = (\x -> getLeft) #-}
{-# COMPILE GHC getRight = (\x -> getRight) #-}


data nativeNode (A : Set) : Set where
  LLConstr : (a : A)(left right : NativeMaybe (IORef (nativeLL A))) → nativeNode A

{-# COMPILE GHC nativeNode = data LL (LLConstr) #-}
