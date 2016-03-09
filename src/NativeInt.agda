module NativeInt where

open import Data.Integer.Base hiding (_+_)

postulate
  Int : Set
  toInt : ℤ -> Int
  fromInt : Int -> ℤ

{-# COMPILED_TYPE Int Int #-}
{-# COMPILED toInt fromInteger #-}
{-# COMPILED fromInt toInteger #-}
