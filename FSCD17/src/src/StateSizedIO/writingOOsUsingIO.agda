{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --allow-unsolved-metas #-}


module src.StateSizedIO.writingOOsUsingIO where


open import src.StateSizedIO.Object
open import src.StateSizedIO.Base
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Bool
open import Function
open import Data.Unit
open import Data.String
open import src.Unit
open import Data.Bool.Base
open import Relation.Binary.PropositionalEquality
open import src.SizedIO.Console
open import src.SizedIO.Console hiding (main;translateIOConsole)
open import Size
open import src.SizedIO.Base
open import src.StateSizedIO.cellStateDependent
open import src.NativeIO
