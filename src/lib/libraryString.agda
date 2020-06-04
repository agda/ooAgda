module lib.libraryString where

open import Data.String
open import Data.Bool
open import Agda.Builtin.String using ( primStringEquality )
open import Data.String public using ()
                               renaming (toList to primStringToList;
                                        _++_  to _++Str_)

_==Str_ : String → String → Bool
_==Str_ = primStringEquality
