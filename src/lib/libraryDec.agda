module lib.libraryDec where

-- old version of Dec
--

open import Data.Empty
open import Level
open import Relation.Nullary using ( ¬_ )

data Dec {p} (P : Set p) : Set p where
  yes : ( p :   P) → Dec P
  no  : (¬p :  ¬ P) → Dec P
