-- {-# OPTIONS --allow-unsolved-metas #-}
module examplesPaperJFP.Coalgebra where

open import Size

F     :  Set → Set
mapF  :  ∀{A B} (f : A → B) → (F A → F B)

--- Dummy implementation to satisfy Agda's positivity checker.
F X       =  X
mapF f x  =  f x

S  :  Set
t  :  S → F S

data S′ : Set where

S = S′
t x = x

record νF : Set where
  coinductive
  field force : F νF

open νF using (force)

{-# TERMINATING #-}
unfoldF : ∀{S} (t : S → F S) → (S → νF)
force (unfoldF t s) = mapF (unfoldF t) (t s)
