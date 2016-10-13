module NativePolyIO where

open import Data.String.Base using (String) public

record Unit {α} : Set α where
  constructor unit

{-# COMPILED_DATA Unit Data.FFI.AgdaUnit () #-}

postulate
  NativeIO     : ∀{α} → Set α → Set α
  nativeReturn : ∀{α}{A : Set α} → A → NativeIO A
  _native>>=_  : ∀{α β}{A : Set α}{B : Set β} → NativeIO A → (A → NativeIO B) → NativeIO B

{-# BUILTIN IO NativeIO #-}
{-# COMPILED_TYPE NativeIO IO.FFI.AgdaIO #-}
{-# COMPILED _native>>=_ (\_ _ _ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b) #-}
{-# COMPILED nativeReturn (\_ _ -> return :: a -> IO a) #-}

postulate
  nativeGetLine   : NativeIO String
  nativePutStrLn  : ∀{α} → String → NativeIO (Unit {α})

{-# COMPILED nativePutStrLn (\ _ s -> putStrLn (Data.Text.unpack s)) #-}
{-# COMPILED nativeGetLine (fmap Data.Text.pack getLine) #-}
