module drawingProgram where 

open import Unit
open import Data.Bool.Base 
open import Data.Char.Base renaming (primCharEquality to charEquality)
open import Data.Nat.Base hiding (_≟_;_⊓_; _+_; _*_)
open import Data.List.Base hiding (_++_)
open import Data.Integer.Base hiding (suc)
open import Data.String.Base
open import Data.Maybe.Base
open import NativeIO

open import Function

open import Size renaming (Size to AgdaSize)

open import SizedIO.Base
open import SizedIO.IOGraphicsLib hiding (GraphicsCommands; GraphicsResponses; GraphicsInterface; IOGraphics; getWindowEvent; openWindow; drawInWindow; closeWindow; translateIOGraphicsLocal; translateIOGraphics)

open import NativeInt
-- open import NativeIOSafe


data GraphicsCommands  :  Set where
  closeWindow         : Window            → GraphicsCommands
  maybeGetWindowEvent : Window            → GraphicsCommands
  getWindowEvent      : Window            → GraphicsCommands
  openWindowNotEx     : String → Size    → GraphicsCommands
  openWindow          : String → (Maybe Point) → (Maybe Size) 
                        → RedrawMode → (Maybe Word32) → GraphicsCommands
  timeGetTime         :                      GraphicsCommands
  drawInWindow        : Window → Graphic → GraphicsCommands
  print               : String →             GraphicsCommands


GraphicsResponses  :                       GraphicsCommands → Set
GraphicsResponses (maybeGetWindowEvent w) = Maybe Event
GraphicsResponses (getWindowEvent w)      = Event
GraphicsResponses (closeWindow w)         = Unit
GraphicsResponses (openWindowNotEx s s')  = Window
GraphicsResponses (openWindow s p s' r w) = Window
GraphicsResponses timeGetTime             = Word32
GraphicsResponses _                       = Unit


GraphicsInterface            :  IOInterface
Command   GraphicsInterface  =  GraphicsCommands
Response  GraphicsInterface  =  GraphicsResponses

IOGraphics : AgdaSize → Set → Set
IOGraphics i = IO GraphicsInterface i


translateIOGraphicsLocal : (c : GraphicsCommands) → NativeIO (GraphicsResponses c)
translateIOGraphicsLocal (maybeGetWindowEvent w) = nativeMaybeGetWindowEvent w
translateIOGraphicsLocal (getWindowEvent w)      = nativeGetWindowEvent w
translateIOGraphicsLocal (closeWindow w)         = nativeCloseWindow w
translateIOGraphicsLocal (openWindowNotEx str size)   = nativeOpenWindow str size
translateIOGraphicsLocal (openWindow str point size mode word) = nativeOpenWindowEx str point size mode word
translateIOGraphicsLocal timeGetTime             = nativeTimeGetTime
translateIOGraphicsLocal (drawInWindow w g)      = nativeDrawInWindow w g
translateIOGraphicsLocal (print s)             = nativePutStrLn s


translateIOGraphics : {A : Set} → IOGraphics ∞ A → NativeIO A
translateIOGraphics = translateIO translateIOGraphicsLocal


integerLess     :  ℤ →  ℤ → Bool
integerLess x y with ∣(y - (x ⊓ y))∣
... | zero = true
... | z = false

line : Point → Point → Graphic
line p  newpoint = withColor red (polygon
                       (nativePoint x y
                        ∷ nativePoint a b
                        ∷ nativePoint (a + xAddition) (b + yAddition)
                        ∷ nativePoint (x + xAddition) (y + yAddition)
                        ∷ [] ) )
  where
  x = nativeProj1Point p
  y = nativeProj2Point p
  a = nativeProj1Point newpoint
  b = nativeProj2Point newpoint

  diffx = + ∣ (a - x) ∣
  diffy = + ∣ (b - y) ∣

  diffx*3 = diffx * (+ 3)
  diffy*3 = diffy * (+ 3)

  condition = (integerLess diffx diffy*3) ∧ (integerLess diffy diffx*3)

  xAddition = if condition then + 2 else + 1
  yAddition = if condition then + 2 else + 1



State = Maybe Point

loop                 :  ∀{i} → Window → State → IOGraphics i Unit
force (loop w s)     =  do'  (getWindowEvent w)
  λ{  (Key c t)     →  if charEquality c 'x' then do (closeWindow w) return
                        else  loop w s  
   ; (MouseMove p₂) →  case s of
                        λ{ nothing  → loop w (just p₂) ;
                          (just p₁) → do (drawInWindow w (line p₁ p₂)) λ _ →
                                       loop w (just p₂)     }
   ; _               →  loop w  s  }


program : ∀{i} → IOGraphics i Unit
program =
  do (openWindow "Drawing Program" nothing (just (size (+ 1000) (+ 1000)))
       nativeDrawGraphic nothing) λ window →
  loop window nothing

main : NativeIO Unit
main = nativeRunGraphics (translateIOGraphics program)





