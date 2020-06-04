module Sized.SelfRef where

open import Data.Product
open import Data.String.Base

open import Size

open import SizedIO.Object
open import SizedIO.IOObject
open import SizedIO.ConsoleObject

open import SizedIO.Base
open import SizedIO.Console hiding (main)

open import NativeIO


data AMethod : Set where
    print :  AMethod
    m1    :  AMethod
    m2    :  AMethod

AResult : (c : AMethod) → Set
AResult _  =  Unit

aI : Interface
Method  aI  =  AMethod
Result  aI  =  AResult

aC : (i : Size) → Set
aC i = ConsoleObject i aI

--
--  Self Referential: method 'm1' calls method 'm2'
--
{-# NON_TERMINATING #-}
aP :  ∀{i} (s : String) → aC i
method (aP s) print =
  exec1 (putStrLn s) >>
  return (_ , aP s)

method (aP s) m1 =
  exec1 (putStrLn s) >>
  method (aP s) m2  >>= λ{ (_ , c₀) →
  return (_ , c₀) }
method (aP s) m2 =
  return (_ , aP (s ++ "->m2"))


program : String → IOConsole ∞ Unit
program arg =
  let c₀ = aP ("start̄") in
  method c₀ m1  >>= λ{ (_ , c₁) →   --- ===> m1 called, then m2 prints out text
  method c₁ print  >>= λ{ (_ , c₂) →
  exec1 (putStrLn "end")        }}

main : NativeIO Unit
main = translateIOConsole (program "")
