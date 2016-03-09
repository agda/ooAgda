module StateSized.GUI.SpaceShipExtendedExample where

 
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
  moveSpaceShipM          :   Point → Frame → GraphicServerMethod
  repaintM                :   Frame → GraphicServerMethod

GraphicServerResult : GraphicServerMethod  →  Set 
GraphicServerResult _ = Unit

GraphicServerInterface : Interface
Method GraphicServerInterface  = GraphicServerMethod
Result GraphicServerInterface  = GraphicServerResult

GraphicServerObject : ∀{i} → Set
GraphicServerObject {i} = IOObject GuiLev1Interface GraphicServerInterface i

graphicServerObject : ∀{i} → Point → GraphicServerObject {i}
method (graphicServerObject (x , y)) (onPaintM dc rect) = 
               do (drawBitmap dc ship (x , y) true) λ _ → 
               return (_ , graphicServerObject (x , y))
method (graphicServerObject (x , y)) (moveSpaceShipM (deltaX , deltaY) fra) = 
               return (_ , graphicServerObject ((x + deltaX) , (y + deltaY)))
method (graphicServerObject (x , y)) (repaintM fra) = 
               do (repaint fra)                λ _ → 
               return (_ , graphicServerObject (x , y)) 

VarType : Set
VarType = GraphicServerObject {∞}

varInit : VarType 
varInit = graphicServerObject ((+ 150) , (+ 150))


onPaint  : ∀{i} → VarType   → DC → Rect → IO GuiLev1Interface i VarType  
onPaint obj dc rect = mapIO proj₂  (method obj (onPaintM dc rect)) 


moveSpaceShip : ∀{i} → Point → Frame → VarType  → IO GuiLev1Interface i VarType 
moveSpaceShip p fra obj = mapIO proj₂ (method obj (moveSpaceShipM p fra))


callRepaint  : ∀{i} → Frame → VarType  → IO GuiLev1Interface i VarType  
callRepaint fra obj = mapIO proj₂ (method obj (repaintM fra))


program : ∀{i} → IOˢ GuiLev2Interface i (λ _ → Unit) []
program =  doˢ (level1C makeFrame)           λ fra →
           doˢ (level1C (makeButton fra))    λ bt →
           doˢ (level1C (addButton fra bt))  λ _ →
           doˢ (createVar varInit)           λ _ → 
           doˢ (setButtonHandler bt (moveSpaceShip (+ 20 , + 0) fra 
                                     ∷ [ callRepaint fra ])) λ _ →
           doˢ (setKeyHandler bt
             (moveSpaceShip (+ 20 , + 0) fra ∷ [ callRepaint fra ])
             (moveSpaceShip (-[1+ 20 ] , + 0) fra ∷ [ callRepaint fra ])
             (moveSpaceShip (+ 0 , -[1+ 20 ]) fra ∷ [ callRepaint fra ])
             (moveSpaceShip (+ 0 , + 20) fra ∷ [ callRepaint fra ]))
             λ _ →
                                     
           doˢ (setOnPaint fra [ onPaint  ])  
           returnˢ 

main : NativeIO Unit
main = start (translateLev2 program)


