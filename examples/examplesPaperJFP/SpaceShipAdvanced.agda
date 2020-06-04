module examplesPaperJFP.SpaceShipAdvanced where


open import SizedIO.Base
open import StateSizedIO.GUI.BaseStateDependent


open import Data.Bool.Base
open import Data.List.Base
open import Data.Integer

open import Data.Product hiding (map)
open import SizedIO.Object
open import SizedIO.IOObject

open import NativeIO
open import Size

open import StateSizedIO.GUI.WxBindingsFFI
open import StateSizedIO.GUI.VariableList

open import StateSizedIO.GUI.WxGraphicsLib

open import StateSized.GUI.BitMaps

data GraphicServerMethod : Set where
  onPaintM               :   DC     →  Rect → GraphicServerMethod
  moveSpaceShipM         :   Frame  →  GraphicServerMethod
  callRepaintM           :   Frame  →  GraphicServerMethod

GraphicServerResult : GraphicServerMethod  →  Set
GraphicServerResult _ = Unit


GraphicServerInterface : Interface
Method  GraphicServerInterface  =  GraphicServerMethod
Result  GraphicServerInterface  =  GraphicServerResult

GraphicServerObject : ∀{i} → Set
GraphicServerObject {i} = IOObject GuiLev1Interface GraphicServerInterface i

graphicServerObject : ∀{i} → ℤ → GraphicServerObject {i}
method (graphicServerObject z) (onPaintM dc rect) =
            exec (drawBitmap dc ship (z , (+ 150)) true) λ _ →
            return (unit , graphicServerObject z)
method (graphicServerObject z) (moveSpaceShipM fra) =
            return (unit , graphicServerObject (z + (+ 20)))
method (graphicServerObject z) (callRepaintM fra) =
            exec (repaint fra)                λ _ →
            return (unit , graphicServerObject z)

VarType = GraphicServerObject {∞}

varInit : VarType
varInit = graphicServerObject (+ 150)


onPaint  : ∀{i} → VarType   → DC → Rect → IO GuiLev1Interface i VarType
onPaint obj dc rect = mapIO proj₂  (method obj (onPaintM dc rect))

moveSpaceShip : ∀{i} → Frame → VarType  → IO GuiLev1Interface i VarType
moveSpaceShip fra obj =  mapIO proj₂ (method obj (moveSpaceShipM fra))

callRepaint  : ∀{i} → Frame → VarType  → IO GuiLev1Interface i VarType
callRepaint fra obj = mapIO proj₂ (method obj (callRepaintM fra))


buttonHandler : ∀{i} → Frame → List (VarType  → IO GuiLev1Interface i VarType)
buttonHandler fra = moveSpaceShip fra ∷ [ callRepaint fra ]


program : ∀{i} → IOˢ GuiLev2Interface i (λ _ → Unit) []
program =  execˢ  (level1C makeFrame)           λ fra →
           execˢ  (level1C (makeButton fra))    λ bt →
           execˢ  (level1C (addButton fra bt))  λ _ →
           execˢ  (createVar varInit)     λ _ →
           execˢ  (setButtonHandler bt
                (moveSpaceShip fra ∷ [ callRepaint fra ])) λ _ →
           execˢ  (setOnPaint fra [ onPaint  ])
           returnˢ

main : NativeIO Unit
main = start (translateLev2 program)
