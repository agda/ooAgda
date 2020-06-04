module examplesPaperJFP.Collatz where

open import Data.Nat.Base
open import Data.Nat.DivMod
open import Data.Fin using (Fin; zero; suc)

open import examplesPaperJFP.Colists

collatzStep            :  ℕ → ListF ℕ ℕ
collatzStep 1          =  nil
collatzStep n          with n divMod 2
... | result q zero _  =  cons n q
... | _                =  cons n (1 + 3 * n)

collatzSequence  :  ℕ → Colist ℕ
collatzSequence  =  unfold collatzStep

open Colist
open import Data.List

displayList : Colist ℕ → ℕ → List ℕ
displayList s 0 = []
displayList s (suc m) with  force s
... | nil = []
... | (cons k s′) =  k ∷ displayList s′ m


displayCollatz : ℕ → ℕ → List ℕ
displayCollatz n m = displayList (collatzSequence n) m
