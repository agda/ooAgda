module NativeInt where

open import Data.Integer.Base hiding (_+_)

postulate
  Int : Set
  toInt : ℤ -> Int
  fromInt : Int -> ℤ

{-# COMPILE GHC Int = type Int #-}
{-# COMPILE GHC toInt fromInteger #-}
{-# COMPILE GHC fromInt toInteger #-}
