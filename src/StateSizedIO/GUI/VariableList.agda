module StateSizedIO.GUI.VariableList where

open import Data.Product hiding (map)
open import Data.List

open import NativeIO
open import StateSizedIO.GUI.WxBindingsFFI 



data VarList : Set₁ where
  []     : VarList
  addVar : (A : Set) → Var A → VarList → VarList


prod : VarList → Set
prod [] = Unit
prod (addVar A v []) = A
prod (addVar A v l)  = A × prod l

takeVar : (l : VarList) → NativeIO (prod l)
takeVar [] = nativeReturn _
takeVar (addVar A v []) = nativeTakeVar {A} v  native>>= λ a → 
                         nativeReturn a 
takeVar (addVar A v (addVar B v' l))  = nativeTakeVar {A} v        native>>= λ a → 
                                       takeVar (addVar B v' l)    native>>= λ rest → 
                                       nativeReturn ( a , rest )



putVar : (l : VarList) → prod l → NativeIO Unit
putVar  [] _ = nativeReturn _
putVar  (addVar A v []) a         = nativePutVar {A} v a 
putVar  (addVar A v (addVar B v' l)) (a , rest) 
                                  = nativePutVar {A} v a         native>>= λ _ → 
                                    putVar (addVar B v' l)  rest native>>= 
                                    nativeReturn 

dispatch : (l : VarList) → (prod l → NativeIO (prod l)) → NativeIO Unit
dispatch l f = takeVar l     native>>= λ a → 
               f a          native>>= λ a₁ → 
               putVar l a₁

dispatchList : (l : VarList) → List (prod l → NativeIO (prod l)) → NativeIO Unit
dispatchList l []         = nativeReturn _
dispatchList l (p ∷ rest) = dispatch l p native>>= λ _ → 
                            dispatchList l rest
