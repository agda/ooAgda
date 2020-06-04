module examplesPaperJFP.SpaceShipCell where


open import SizedIO.Base
open import StateSizedIO.GUI.BaseStateDependent


open import Data.Bool.Base
open import Data.List.Base
open import Data.Integer

open import Data.Product hiding (map)
open import SizedIO.Object
open import SizedIO.IOObject

open import NativeIO
open import Sized.SimpleCell hiding (main; program)

open import StateSizedIO.GUI.WxBindingsFFI
open import StateSizedIO.GUI.VariableList

open import StateSizedIO.GUI.WxGraphicsLib

open import StateSized.GUI.BitMaps


VarType  = Object (cellJ ℤ)

cellℤC : (z : ℤ ) → VarType
objectMethod (cellℤC z) get       = (  z     ,  cellℤC z   )
objectMethod (cellℤC z) (put z′)  = (  unit  ,  cellℤC z′  )

varInit : VarType
varInit = cellℤC (+ 150)


onPaint  : ∀{i} → VarType   → DC → Rect → IO GuiLev1Interface i VarType


onPaint c dc rect =
  let (z , c₁) = objectMethod c get                in
  exec  (drawBitmap dc ship (z , (+ 150)) true)  λ _ →
  return c₁

moveSpaceShip : ∀{i} → Frame → VarType
                     → IO GuiLev1Interface i VarType

moveSpaceShip fra c =
  let  (z  ,  c₁)  =  objectMethod c   get
       (_  ,  c₂)  =  objectMethod c₁  (put (z + (+ 20)))
  in   return c₂

callRepaint  : ∀{i} → Frame → VarType → IO GuiLev1Interface i VarType


callRepaint fra c = exec (repaint fra) λ _ →  return c


program : ∀{i} → IOˢ GuiLev2Interface i (λ _ → Unit) []
program =  execˢ (level1C makeFrame)           λ fra →
           execˢ (level1C (makeButton fra))    λ bt →
           execˢ (level1C (addButton fra bt))  λ _ →
           execˢ (createVar varInit)  λ _ →
           execˢ (setButtonHandler bt (moveSpaceShip fra
                                     ∷ [ callRepaint fra ])) λ _ →
           execˢ (setOnPaint       fra [ onPaint  ])
           returnˢ

main : NativeIO Unit
main = start (translateLev2 program)
