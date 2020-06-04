module SizedIO.Object where

open import Data.Product

record Interface : Set₁ where
  field
    Method  : Set
    Result  : (m : Method) → Set
open Interface public

-- A simple object just returns for a method the response
-- and the object itself
record Object (i : Interface) : Set where
  coinductive
  field
    objectMethod : (m : Method i) → Result i m × Object i

open Object public


_▹_ : {A : Set} → {B : Set} → A → (A → B) → B
a ▹ f = f a
