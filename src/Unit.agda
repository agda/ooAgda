
module Unit where

record Unit : Set where
  constructor unit

{-# COMPILE GHC Unit = data () (()) #-}
