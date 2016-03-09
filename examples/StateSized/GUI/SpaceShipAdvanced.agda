module StateSized.GUI.SpaceShipAdvanced where


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

open import StateSized.GUI.ShipBitMap

data GraphicServerMethod : Set where
  onPaintM                :   DC → Rect → GraphicServerMethod
  moveSpaceShipM          :   Frame → GraphicServerMethod
  repaintM                :   Frame → GraphicServerMethod

GraphicServerResult : GraphicServerMethod  →  Set 
GraphicServerResult _ = Unit

GraphicServerInterface : Interface
Method GraphicServerInterface  = GraphicServerMethod
Result GraphicServerInterface  = GraphicServerResult

GraphicServerObject : ∀{i} → Set
GraphicServerObject {i} = IOObject GuiLev1Interface GraphicServerInterface i

graphicServerObject : ∀{i} → ℤ → GraphicServerObject {i}
method (graphicServerObject z) (onPaintM dc rect) = 
               do (drawBitmap dc ship (z , (+ 150)) true) λ _ →  
               return (_ , graphicServerObject z)
method (graphicServerObject z) (moveSpaceShipM fra) = 
               return (_ , graphicServerObject (z + + 20))
method (graphicServerObject z) (repaintM fra) = 
               do (repaint fra)                λ _ → 
               return (_ , graphicServerObject z) 

VarType : Set
VarType = GraphicServerObject {∞}

varInit : VarType 
varInit = graphicServerObject (+ 150)


onPaint  : ∀{i} → VarType   → DC → Rect → IO GuiLev1Interface i VarType  
onPaint obj dc rect = mapIO proj₂  (method obj (onPaintM dc rect)) 


moveSpaceShip : ∀{i} → Frame → VarType  → IO GuiLev1Interface i VarType 
moveSpaceShip fra obj = mapIO proj₂ (method obj (moveSpaceShipM fra))


callRepaint  : ∀{i} → Frame → VarType  → IO GuiLev1Interface i VarType  
callRepaint fra obj = mapIO proj₂ (method obj (repaintM fra))


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


