module examplesPaperJFP.Equality where

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

-- obsolete, now in Agda.Builtin.Equality: {-# BUILTIN EQUALITY _≡_ #-}
--  No longer exists in Agda: {-# BUILTIN REFL refl #-}
