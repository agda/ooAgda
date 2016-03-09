module StateSized.GUI.SpaceShipSimpleVar where

open import SizedIO.Base
open import StateSizedIO.GUI.BaseStateDependent 

open import Data.Bool.Base
open import Data.List.Base
open import Data.Integer

open import Data.Product hiding (map)
open import SizedIO.Object
open import SizedIO.IOObject

open import NativeIO

open import StateSizedIO.GUI.WxBindingsFFI 
open import StateSizedIO.GUI.VariableList

open import StateSizedIO.GUI.WxGraphicsLib

open import StateSized.GUI.ShipBitMap

VarType : Set
VarType = ℤ

varInit : VarType 
varInit = (+ 150)

onPaint  : ∀{i} → VarType   → DC → Rect → IO GuiLev1Interface i VarType  
onPaint  z dc rect = do (drawBitmap dc ship (z , (+ 150)) true) λ _ → 
                     return z 


moveSpaceShip : ∀{i} → Frame → VarType  → IO GuiLev1Interface i VarType 
moveSpaceShip fra z   = return (z + + 20) 

callRepaint : ∀{i} → Frame → VarType  → IO GuiLev1Interface i VarType  
callRepaint fra z   = do (repaint fra) λ _  →  
                       return z

program : ∀{i} → IOˢ GuiLev2Interface i (λ _ → Unit) []
program =  doˢ (level1C makeFrame)           λ fra →
           doˢ (level1C (makeButton fra))    λ bt →
           doˢ (level1C (addButton fra bt))  λ _ →
           doˢ (createVar varInit)           λ _ → 
           doˢ (setButtonHandler bt (moveSpaceShip fra 
                                     ∷ [ callRepaint fra ])) λ _ →
           doˢ (setOnPaint fra [ onPaint  ])  
           returnˢ 

main : NativeIO Unit
main = start (translateLev2 program)

