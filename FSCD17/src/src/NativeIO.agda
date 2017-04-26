module src.NativeIO where

open import src.Unit public
open import Data.List
open import Data.Nat
open import Data.String.Base using (String) public

{-# FOREIGN GHC import qualified Data.Text #-}
{-# FOREIGN GHC import qualified System.Environment #-}


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

{-# COMPILE GHC nativePutStrLn = (\ s -> putStrLn (Data.Text.unpack s)) #-}
{-# COMPILE GHC nativeGetLine = (fmap Data.Text.pack getLine) #-}


postulate
  getArgs : NativeIO (List String)
  primShowNat : ℕ → String

{-# COMPILE GHC primShowNat = Data.Text.pack . show #-}

{-# COMPILE GHC getArgs =     fmap (map Data.Text.pack) System.Environment.getArgs #-}



--
-- Debug function
--
{-# FOREIGN GHC import qualified Debug.Trace as Trace #-}

{-# FOREIGN GHC

debug = flip Trace.trace

debug' :: c -> Data.Text.Text -> c
debug' c txt = debug c (Data.Text.unpack txt)

#-}

postulate debug : {A : Set} →  A → String → A
--debug {A} a s = a
{-# COMPILE GHC debug = (\x -> debug') #-}

postulate debug₁ : {A : Set₁} →  A → String → A
-- debug₁ {A} a s = a
{-# COMPILE GHC debug₁ = (\x -> debug') #-}
