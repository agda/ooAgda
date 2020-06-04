module examplesPaperJFP.finn where

open import Data.Nat

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

mutual
  data Even : ℕ → Set where
    0p    : Even 0
    sucp  : {n : ℕ}  →  Odd n   →  Even  (suc  n)

  data Odd : ℕ → Set where
    sucp  : {n : ℕ}  →  Even n  →  Odd   (suc  n)
