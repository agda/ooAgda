module examplesPaperJFP.NativeIOSafe where

open import Data.Maybe.Base using (Maybe; nothing; just) public
open import Data.String.Base using (String) public

record Unit : Set where
  constructor unit

{-# COMPILE GHC Unit = () #-}

postulate
  NativeIO     : Set → Set
  nativeReturn : {A : Set} → A → NativeIO A
  _native>>=_  : {A B : Set} → NativeIO A → (A → NativeIO B) → NativeIO B


{-# BUILTIN IO NativeIO #-}
{-# COMPILE GHC NativeIO = IO #-}   -- IO.FF-I.AgdaIO
{-# COMPILE GHC _native>>=_ = (\_ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b) #-}
{-# COMPILE GHC nativeReturn = (\_ -> return :: a -> IO a) #-}

postulate
  nativeGetLine   : NativeIO (Maybe String)
  nativePutStrLn  : String → NativeIO Unit

{-# FOREIGN GHC import Data.Text #-}
{-# FOREIGN GHC import System.IO.Error #-}

{-# COMPILE GHC nativePutStrLn = (\ s -> putStrLn (Data.Text.unpack s)) #-}
{-# COMPILE GHC nativeGetLine = (fmap (Just . Data.Text.pack) getLine `System.IO.Error.catchIOError` \ err -> if System.IO.Error.isEOFError err then return Nothing else ioError err) #-}
