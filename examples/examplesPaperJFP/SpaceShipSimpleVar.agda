module examplesPaperJFP.SpaceShipSimpleVar where

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

open import StateSized.GUI.BitMaps

VarType = ℤ

varInit : VarType
varInit = (+ 150)


onPaint : ∀{i} → VarType → DC → Rect → IO GuiLev1Interface i VarType
onPaint z dc rect      =  exec (drawBitmap dc ship (z , (+ 150)) true) λ _ →
                          return z

moveSpaceShip  : ∀{i} → Frame → VarType → IO GuiLev1Interface i VarType
moveSpaceShip  fra z   =  return (z + (+ 20))

callRepaint    : ∀{i} → Frame → VarType → IO GuiLev1Interface i VarType
callRepaint    fra z   =  exec (repaint fra) λ _ → return z


buttonHandler : ∀{i} → Frame → List (VarType  → IO GuiLev1Interface i VarType)
buttonHandler fra = moveSpaceShip fra ∷ [ callRepaint fra ]

program : ∀{i} → IOˢ GuiLev2Interface i (λ _ → Unit) []
program =  execˢ (level1C makeFrame)           λ fra →
           execˢ (level1C (makeButton fra))    λ bt →
           execˢ (level1C (addButton fra bt))  λ _ →
           execˢ (createVar varInit)           λ _ →
           execˢ (setButtonHandler bt (moveSpaceShip fra
                                     ∷ [ callRepaint fra ])) λ _ →
           execˢ (setOnPaint       fra [ onPaint  ])
           returnˢ

main : NativeIO Unit
main = start (translateLev2 program)
