module spaceShipCell where

open import Unit
open import Data.List.Base hiding ([])
open import Data.Bool.Base
open import Data.Integer
open import Data.Product hiding (map)
open import NativeIO

open import SizedIO.Object
open import SizedIO.IOObject
open import StateSizedIO.GUI.WxBindingsFFI
open import StateSizedIO.GUI.WxGraphicsLib
open import StateSized.GUI.ShipBitMap
open import SizedIO.Base
open import StateSizedIO.GUI.BaseStateDependent
open import StateSizedIO.GUI.VariableList
open import Sized.SimpleCell hiding (main; program)

VarType  = Object (cellI ℤ)

cellℤC : (z : ℤ ) → VarType
objectMethod (cellℤC z) get       = (  z  ,  cellℤC z   )
objectMethod (cellℤC z) (put z')  = (  _  ,  cellℤC z'  )

varInit : VarType
varInit = cellℤC (+ 150)

onPaint : ∀{i} → VarType → DC → Rect → IO GuiLev1Interface i VarType
onPaint c dc rect =
  let (z , c₁) = objectMethod c get                in
  do  (drawBitmap dc ship (z , (+ 150)) true)  λ _ →
  return c₁

moveSpaceShip  : ∀{i} → Frame → VarType → IO GuiLev1Interface i VarType
moveSpaceShip fra c =
  let  (z  ,  c₁)  =  objectMethod c   get
       (_  ,  c₂)  =  objectMethod c₁  (put (z + + 20))
  in   return c₂

callRepaint    : ∀{i} → Frame → VarType → IO GuiLev1Interface i VarType
callRepaint fra c = do (repaint fra) λ _ →  return c


buttonHandler : ∀{i} → Frame → List (VarType  → IO GuiLev1Interface i VarType)
buttonHandler fra = moveSpaceShip fra ∷ [ callRepaint fra ]

program : ∀{i} → IOˢ GuiLev2Interface i (λ _ → Unit) []
program =  doˢ (level1C makeFrame)           λ fra →
           doˢ (level1C (makeButton fra))    λ bt →
           doˢ (level1C (addButton fra bt))  λ _ →
           doˢ (createVar varInit)           λ _ →
           doˢ (setButtonHandler bt (buttonHandler fra)) λ _ →
           doˢ (setOnPaint       fra [ onPaint  ])
           returnˢ

main : NativeIO Unit
main = start (translateLev2 program)
