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

open import StateSized.GUI.BitMaps



spaceShipMove = 10

data RockMethod : Set where
  move : RockMethod
  getPoint : RockMethod
  draw : DC → Rect → RockMethod

RockResult : RockMethod → Set
RockResult getPoint = Point
RockResult _        = Unit

RockInterface : Interface
Method RockInterface = RockMethod
Result RockInterface = RockResult

RockObject : ∀{i} → Set
RockObject {i} = IOObject GuiLev1Interface RockInterface i

rockObject : ∀{i} → Point → RockObject {i}
method (rockObject (x , y)) move =
  return ( _ , rockObject (x , (y + (+ 2))))
method (rockObject p) (draw dc rect) =
  exec (drawBitmap dc rock p true) λ _ →
  return (_ , rockObject p)
method (rockObject p) getPoint =
  return (p , rockObject p)

data SpaceshipMethod : Set where
  move : Point → SpaceshipMethod
  draw : DC → Rect → SpaceshipMethod
  collide : RockObject → SpaceshipMethod

SpaceshipResult : SpaceshipMethod  →  Set
SpaceshipResult _  = Unit

SpaceshipInterface : Interface
Method SpaceshipInterface = SpaceshipMethod
Result SpaceshipInterface = SpaceshipResult

SpaceshipObject : ∀{i} → Set
SpaceshipObject {i} = IOObject GuiLev1Interface SpaceshipInterface i

spaceshipObject : ∀{i} → Point → SpaceshipObject {i}
method (spaceshipObject (x , y)) (move (deltaX , deltaY)) =
  return ( _ , spaceshipObject ((x + deltaX) , (y + deltaY)))
method (spaceshipObject p) (draw dc rect) =
  exec (drawBitmap dc ship p true) λ _ →
       return (_ , spaceshipObject p)
method (spaceshipObject p) (collide rock) =
   return (_ , spaceshipObject p)





data GraphicServerMethod : Set where
  onPaintM                :   DC → Rect → GraphicServerMethod
  repaintM                :   Frame → GraphicServerMethod
  moveSpaceShipM          :   Point → GraphicServerMethod
  moveWorldM              :   GraphicServerMethod

GraphicServerResult : GraphicServerMethod  →  Set
GraphicServerResult _ = Unit

GraphicServerInterface : Interface
Method GraphicServerInterface  = GraphicServerMethod
Result GraphicServerInterface  = GraphicServerResult

GraphicServerObject : ∀{i} → Set
GraphicServerObject {i} = IOObject GuiLev1Interface GraphicServerInterface i



graphicServerObject : ∀{i} → SpaceshipObject → RockObject →
                             GraphicServerObject {i}
method (graphicServerObject ship rock) (onPaintM dc rect) =
               method ship (draw dc rect) >>= λ { (_ , ship') →
               method rock (draw dc rect) >>= λ { (_ , rock') →
               return (_ , graphicServerObject ship' rock') }}
method (graphicServerObject ship rock) (repaintM fra) =
               exec (repaint fra)                λ _ →
               return (_ , graphicServerObject ship rock)
method (graphicServerObject ship rock) (moveSpaceShipM (deltaX , deltaY)) =
               method ship (move (deltaX , deltaY)) >>= λ { (_ , ship') →
               return (_ , graphicServerObject ship' rock) }
method (graphicServerObject ship rock) moveWorldM =
               method rock move >>= λ { (_ , rock') →
               return (_ , graphicServerObject ship rock') }




VarType : Set
VarType = GraphicServerObject {∞}

varInit : VarType
varInit = graphicServerObject (spaceshipObject (+ 150 , + 150))
                              (rockObject (+ 20 , + 10))


onPaint  : ∀{i} → VarType → DC → Rect → IO GuiLev1Interface i VarType
onPaint obj dc rect = mapIO proj₂  (method obj (onPaintM dc rect))


moveSpaceShip : ∀{i} → Point → VarType  → IO GuiLev1Interface i VarType
moveSpaceShip p obj = mapIO proj₂ (method obj (moveSpaceShipM p))

moveWorld : ∀{i} → VarType  → IO GuiLev1Interface i VarType
moveWorld obj = mapIO proj₂ (method obj moveWorldM)


callRepaint  : ∀{i} → Frame → VarType  → IO GuiLev1Interface i VarType
callRepaint fra obj = mapIO proj₂ (method obj (repaintM fra))


program : ∀{i} → IOˢ GuiLev2Interface i (λ _ → Unit) []
program =  execˢ (level1C makeFrame)           λ fra →
           execˢ (level1C (makeButton fra))    λ bt →
           execˢ (level1C (addButton fra bt))  λ _ →
           execˢ (createVar varInit)           λ _ →
           execˢ (setButtonHandler bt (moveSpaceShip (+ 20 , + 0)
                                     ∷ [ callRepaint fra ])) λ _ →
           execˢ (setKeyHandler bt
             (moveSpaceShip (+ spaceShipMove , + 0)  ∷ [ callRepaint fra ])
             (moveSpaceShip (-[1+ spaceShipMove ] , + 0) ∷ [ callRepaint fra ])
             (moveSpaceShip (+ 0 , -[1+ spaceShipMove ]) ∷ [ callRepaint fra ])
             (moveSpaceShip (+ 0 , + spaceShipMove) ∷ [ callRepaint fra ]))
             λ _ →

           execˢ (setOnPaint fra ([ onPaint  ]))  λ _ →
           execˢ (setTimer fra (+ 50)
               (moveWorld ∷ [ callRepaint fra ]))  λ _ →
           returnˢ unit

main : NativeIO Unit
main = (start (translateLev2 program)) native>>= (λ _ → nativePutStrLn "stephan test2")
