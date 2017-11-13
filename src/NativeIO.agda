module NativeIO where

open import Unit public
open import Data.String.Base using (String) public

postulate
  NativeIO     : Set → Set
  nativeReturn : {A : Set} → A → NativeIO A
  _native>>=_  : {A B : Set} → NativeIO A → (A → NativeIO B) → NativeIO B

{-# BUILTIN IO NativeIO #-}
{-# COMPILE GHC NativeIO = type IO #-}
{-# COMPILE GHC nativeReturn = (\_ -> return :: a -> IO a) #-}
{-# COMPILE GHC _native>>=_ = (\_ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b) #-}

postulate
  nativeGetLine   : NativeIO String
  nativePutStrLn  : String → NativeIO Unit

{-# COMPILED nativePutStrLn (\ s -> putStrLn (Data.Text.unpack s)) #-}
{-# COMPILED nativeGetLine (fmap Data.Text.pack getLine) #-}
