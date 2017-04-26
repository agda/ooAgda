
module src.Unit where

record Unit : Set where
  constructor unit

{-# COMPILED_DATA Unit () () #-}
