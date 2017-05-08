module examples.heap.ALL where

-- Correctness Properties
--
open import examples.heap.correctnessLinkedList

open import examples.heap.correctnessLinkedListStep2

-- World Predicates
--
open import src.heap.worldModule

-- Generic Heap
--
open import src.heap.heapAsObjectGeneric

-- Store (without Object)
--
open import src.heap.heapAsObjectBase

-- Heap as Object
--
open import src.heap.heapAsObject

-- Session Types/Alebraic Proofs
--
open import examples.heap.correctnessLinkedListExampleProg
open import examples.heap.correctnessLinkedListProofsAlgebraicLaws
open import examples.heap.correctnessLinkedListSessionTypes
open import examples.heap.correctnessLinkedListStep2


-- Example
--
open import src.heap.heapAsObjectExample

-- Native Heap
--
open import src.heap.heapAsObjectNativeHeap

-- Benchmarks
--
open import examples.benchmarks.binaryTreeBenchmark
open import examples.benchmarks.nativeBinaryTree
open import examples.heap.heapEfficient
