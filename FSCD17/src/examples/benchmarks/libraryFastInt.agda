
module examples.benchmarks.libraryFastInt where


open import src.NativeIO renaming ( _native>>=_ to _>>=_;
                               nativeReturn to return;
                                 nativeGetLine to getLine;
                                  nativePutStrLn to  putStrLn)

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.String.Base

infixl 6 _+Int_ _-Int_
infixl 7 _*Int_ modInt
infixr 4 _==Int_


showBool : Bool → String
showBool = λ b → if b then "true" else "false"

postulate
  Int : Set

  _+Int_ : Int → Int → Int
  _-Int_ : Int → Int → Int
  _*Int_ : Int → Int → Int
  _^Int_ : Int → Int → Int

  modInt : Int → Int → Int
  absInt : Int → Int

  _>Int_ : Int → Int → Bool
  _<Int_ : Int → Int → Bool



  _==Int_ : Int → Int → Bool

  showInt : Int → String

  toInt :  ℕ → Int
  fromInt :  Int → ℕ


  &Int : Int → Int → Int



{-# COMPILE GHC Int = type Int #-}

{-# COMPILE GHC _+Int_ = (+) #-}
{-# COMPILE GHC _-Int_ = (-) #-}
{-# COMPILE GHC _*Int_ = (*) #-}
{-# COMPILE GHC _^Int_ = (^) #-}

{-# COMPILE GHC modInt = mod #-}
{-# COMPILE GHC absInt = abs #-}

{-# COMPILE GHC _>Int_ = (>) #-}
{-# COMPILE GHC _<Int_ = (<) #-}

{-# COMPILE GHC _==Int_ = (==) #-}
{-# COMPILE GHC showInt = Data.Text.pack . show #-}
{-# COMPILE GHC toInt = fromIntegral #-}
{-# COMPILE GHC fromInt = fromIntegral #-}

{-# FOREIGN GHC import qualified Data.Bits #-}
{-# COMPILE GHC &Int = (Data.Bits..&.) #-}



{-
main : NativeIO Unit
main = putStrLn ("Print 3==5: " ++ showBool ((toInt 3) ==Int (toInt 5)))
-}
