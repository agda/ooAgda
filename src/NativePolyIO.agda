module NativePolyIO where

open import Data.String.Base using (String) public
open import Level


record Unit {α} : Set α where
  constructor unit

{-# HASKELL type AgdaUnit a = () #-}

{-# COMPILED_DATA Unit AgdaUnit () #-}

postulate
  NativeIO : ∀ {ℓ} → Set ℓ → Set ℓ
  nativeReturn : ∀ {a} {A : Set a} → A → NativeIO A
  _native>>=_  : ∀ {a b} {A : Set a} {B : Set b} → NativeIO A → (A → NativeIO B) → NativeIO B


{-# COMPILED_TYPE NativeIO MAlonzo.Code.NativePolyIO.AgdaIO #-}
{-# BUILTIN IO NativeIO #-}

{-# HASKELL type AgdaIO a b = IO b #-}


{-# COMPILED nativeReturn (\_ _ -> return :: a -> IO a) #-}
{-# COMPILED _native>>=_  (\_ _ _ _ ->
                        (>>=) :: IO a -> (a -> IO b) -> IO b) #-}

{-# IMPORT Data.Text.IO #-}

postulate
  nativePutStrLn : ∀ {ℓ} → String → NativeIO (Unit{ℓ})
  nativeGetLine  : NativeIO String




{-# COMPILED nativePutStrLn (\ _ s -> Data.Text.IO.putStrLn s) #-}
{-# COMPILED nativeGetLine  Data.Text.IO.getLine #-}
