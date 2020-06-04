module examplesPaperJFP.exampleFinFun where

open import examplesPaperJFP.finn

open import Data.Nat

toℕ : ∀ {n} → Fin n → ℕ
toℕ  zero     =  0
toℕ  (suc n)  =  suc (toℕ n)

mutual
  _+e_ : ∀ {n m} →  Even n   →  Even m  →  Even  (n + m)
  0p      +e  p  =  p
  sucp p  +e  q  =  sucp  (p +o q)

  _+o_ : ∀ {n m}  →  Odd n   →  Even m  →  Odd   (n + m)
  sucp p  +o  q  =  sucp  (p +e q)
