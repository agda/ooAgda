module examplesPaperJFP.VariableList where

open import Data.Product hiding (map)
open import Data.List

open import NativeIO
open import StateSizedIO.GUI.WxBindingsFFI
open import Relation.Binary.PropositionalEquality

data VarList : Set₁ where
  []      :  VarList
  addVar  :  (A : Set) → Var A → VarList → VarList


prod : VarList → Set
prod  []               =  Unit
prod  (addVar A v [])  =  A
prod  (addVar A v l)   =  A × prod l




takeVar : (l : VarList) → NativeIO (prod l)
takeVar  []                            = nativeReturn unit
takeVar (addVar A v [])                = nativeTakeVar {A} v
takeVar (addVar A v (addVar B v′ l))   =
  nativeTakeVar {A} v       native>>= λ a →
  takeVar (addVar B v′ l)   native>>= λ rest →
  nativeReturn ( a , rest )

putVar : (l : VarList) → prod l → NativeIO Unit
putVar  [] _                                     = nativeReturn unit
putVar  (addVar A v []) a                        = nativePutVar {A} v a
putVar  (addVar A v (addVar B v′ l)) (a , rest)  =
  nativePutVar {A} v a          native>>= λ _ →
  putVar (addVar B v′ l)  rest
