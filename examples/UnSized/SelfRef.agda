module UnSized.SelfRef where

open import Data.Unit.Base
open import Data.Product
open import Data.String.Base
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)

open import Size
--open import SimpleCell
open import SizedIO.Object
open import SizedIO.IOObject
open import SizedIO.ConsoleObject
-- open import PrimTypeHelpersSmall

open import UnSizedIO.Base hiding (main)
open import UnSizedIO.Console hiding (main)

open import NativeIO
--open import SimpleCell

-- Object Alpha

data AlphaMethod A : Set where
    print : AlphaMethod A
    set : A → AlphaMethod A
    m1 : AlphaMethod A
    m2 : AlphaMethod A

AlphaResponses : {A : Set} (c : AlphaMethod A) → Set
AlphaResponses _  = ⊤


alphaI : (A : Set) → Interface
Method   (alphaI A)   = AlphaMethod A
Result  (alphaI A) m = AlphaResponses m

alphaC : (i : Size) → Set
alphaC i = ConsoleObject i (alphaI String)

--
--  Self Referential: method 'm1' calls method 'm2'
--
-- {-# NON_TERMINATING #-}
alphaO :  ∀{i} (s : String) → alphaC i
method (alphaO s) print =
  do (putStrLn s) >>
  return (_ , alphaO s)

method (alphaO s) (set x) =
  return (_ , alphaO x)

-- force (method (alphaO s) m1) = do (putStrLn s) λ _ →
--   method (alphaO s) m2  >>= λ{ (_ , c₀) →
--   return (_ , c₀) }
method (alphaO s) m1 =
  do1 (putStrLn s) >>
  method (alphaO s) m2  >>= λ{ (_ , c₀) →
  return (_ , c₀) }
method (alphaO s) m2 =
  return (_ , alphaO (s ++ "->m2"))


program : String → IOConsole ∞ Unit
program arg =
  let c₀ = alphaO ("start̄\n====\n\n") in
  method c₀ m1  >>= λ{ (_ , c₁) →   --- ===> m1 called, but m2 prints out text
  method c₁ print  >>= λ{ (_ , c₂) →
  do1 (putStrLn "\n\n====\nend")        }}

main : NativeIO Unit
main = translateIOConsole (program "")
