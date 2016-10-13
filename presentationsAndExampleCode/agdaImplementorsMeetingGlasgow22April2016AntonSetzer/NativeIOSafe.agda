module NativeIOSafe where

open import Data.Maybe.Base using (Maybe; nothing; just) public
open import Data.String.Base using (String) public

record Unit : Set where
  constructor unit

{-# COMPILED_DATA Unit () () #-}

postulate
  NativeIO     : Set → Set
  nativeReturn : {A : Set} → A → NativeIO A
  _native>>=_  : {A B : Set} → NativeIO A → (A → NativeIO B) → NativeIO B

{-# BUILTIN IO NativeIO #-}
{-# COMPILED_TYPE NativeIO IO #-}   -- IO.FFI.AgdaIO
{-# COMPILED _native>>=_ (\_ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b) #-}
{-# COMPILED nativeReturn (\_ -> return :: a -> IO a) #-}

postulate
  nativeGetLine   : NativeIO (Maybe String)
  nativePutStrLn  : String → NativeIO Unit

{-# IMPORT Data.Text #-}
{-# IMPORT System.IO.Error #-}

{-# COMPILED nativePutStrLn (\ s -> putStrLn (Data.Text.unpack s)) #-}
{-# COMPILED nativeGetLine (fmap (Just . Data.Text.pack) getLine `System.IO.Error.catchIOError` \ err -> if System.IO.Error.isEOFError err then return Nothing else ioError err) #-}
