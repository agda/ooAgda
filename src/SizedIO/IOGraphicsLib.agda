module SizedIO.IOGraphicsLib where

{-# FOREIGN GHC import qualified Graphics.SOE #-}
{-# FOREIGN GHC import qualified Graphics.Rendering.OpenGL #-}
{-# FOREIGN GHC import qualified GHC.Int #-}
{-# FOREIGN GHC import qualified Foreign.C.Types #-}

open import Data.Bool.Base
open import Data.Char.Base
open import Data.Nat.Base hiding (_+_)
open import Data.List.Base as L
open import Data.Integer.Base
open import Data.Product

open import Data.Maybe.Base

open import Size renaming (Size to AgdaSize)

open import SizedIO.Base

open import NativeIO
open import NativeInt


AgdaPoint = (ℤ × ℤ)


postulate Window : Set
-- {-# COMPILED_TYPE Window Graphics.SOE.Window #-}

postulate Size : Set
-- {-# COMPILED_TYPE Size Graphics.SOE.Size #-}

postulate size : ℤ → ℤ → Size
-- {-# COMPILED size (\ x y -> ( (fromInteger x) :: Int, (fromInteger y) :: Int) :: Graphics.SOE.Size) #-}


postulate Point : Set
-- {-# COMPILED_TYPE Point Graphics.SOE.Point #-}

postulate nativePoint : ℤ → ℤ → Point
-- {-# COMPILED nativePoint (\ x y -> (fromInteger x, fromInteger y)::Graphics.SOE.Point) #-}

postulate nativeProj1Point : Point → ℤ
postulate nativeProj2Point : Point → ℤ
-- {-# COMPILED nativeProj1Point (\(x, y) -> toInteger x) #-}
-- {-# COMPILED nativeProj2Point (\(x, y) -> toInteger y) #-}

{-
toNativePoint : Point → NativePoint
toNativePoint (x , y) = nativePoint x y 
-}



data Event : Set where
   Key : Char → Bool → Event
   Button : Point → Bool → Bool → Event
   MouseMove : Point → Event
   Resize : Event
   Closed : Event

-- {-# COMPILED_DATA Event Graphics.SOE.Event Graphics.SOE.Key Graphics.SOE.Button Graphics.SOE.MouseMove Graphics.SOE.Resize Graphics.SOE.Closed #-}

postulate nativeMaybeGetWindowEvent : Window → NativeIO (Maybe Event)
-- {-# COMPILED nativeMaybeGetWindowEvent Graphics.SOE.maybeGetWindowEvent #-}

postulate nativeGetWindowEvent : Window → NativeIO (Event)
-- {-# COMPILED nativeGetWindowEvent Graphics.SOE.getWindowEvent #-}


postulate Graphic : Set
-- {-# COMPILED_TYPE Graphic Graphics.SOE.Graphic #-}


postulate nativeDrawInWindow : Window → Graphic → NativeIO Unit
-- {-# COMPILED nativeDrawInWindow Graphics.SOE.drawInWindow #-}


postulate Word32 : Set
-- {-# COMPILED_TYPE Word32 Graphics.SOE.Word32 #-}

postulate text : Point → String → Graphic
-- {-# COMPILED text (\ p s -> Graphics.SOE.text p (Data.Text.unpack s)) #-}


data RedrawMode : Set where
-- (removed from lib where: DoubleBuffered : RedrawMode, Unbuffered : RedrawMode)

-- {-# COMPILED_DATA RedrawMode Graphics.SOE.RedrawMode #-}


postulate nativeDrawGraphic : RedrawMode
-- {-# COMPILED nativeDrawGraphic Graphics.SOE.drawGraphic #-}

postulate nativeDrawBufferedGraphic : RedrawMode
-- {-# COMPILED nativeDrawBufferedGraphic Graphics.SOE.drawBufferedGraphic #-}

postulate nativeOpenWindow : String → Size → NativeIO Window
-- {-# COMPILED nativeOpenWindow (\ s -> Graphics.SOE.openWindow (Data.Text.unpack s)) #-}

postulate nativeOpenWindowEx : String → (Maybe Point) → (Maybe Size) → RedrawMode → (Maybe Word32) → NativeIO Window
-- {-# COMPILED nativeOpenWindowEx (\s -> Graphics.SOE.openWindowEx (Data.Text.unpack s)) #-}

nativeOpenWindowExNat : String → (Maybe Point) → ℕ → ℕ → RedrawMode → (Maybe Word32) → NativeIO Window
nativeOpenWindowExNat s p n1 n2 a b = nativeOpenWindowEx s p (just (size (+ n1) (+ n2))) a b

postulate nativeCloseWindow : Window → NativeIO Unit
-- {-# COMPILED nativeCloseWindow Graphics.SOE.closeWindow #-}




postulate nativeRunGraphics :  NativeIO Unit → NativeIO Unit
-- {-#  COMPILED nativeRunGraphics Graphics.SOE.runGraphics #-}

postulate word32ToInteger : Word32 → ℤ
-- {-#  COMPILED word32ToInteger (\w -> toInteger (Graphics.SOE.word32ToInt w)) #-}

postulate nativeTimeGetTime : NativeIO Word32
-- {-#  COMPILED nativeTimeGetTime Graphics.SOE.timeGetTime #-}


data Color : Set where
  black   : Color
  blue    : Color
  green   : Color
  cyan    : Color
  red     : Color
  magenta : Color
  yellow  : Color
  white   : Color
-- {-#  COMPILED_DATA Color Graphics.SOE.Color Graphics.SOE.Black Graphics.SOE.Blue Graphics.SOE.Green Graphics.SOE.Cyan Graphics.SOE.Red Graphics.SOE.Magenta Graphics.SOE.Yellow Graphics.SOE.White #-}

postulate withColor : Color → Graphic → Graphic
-- {-#  COMPILED withColor Graphics.SOE.withColor #-}

postulate polygon : List Point → Graphic
-- {-#  COMPILED polygon Graphics.SOE.polygon #-}

{-
polygon : List Point → Graphic
polygon l = nativePolygon (L.map toNativePoint l)
-}

data GraphicsCommands : Set where
  closeWindow         : Window            → GraphicsCommands
  maybeGetWindowEvent : Window            → GraphicsCommands
  getWindowEvent      : Window            → GraphicsCommands
  openWindowNotEx     : String → Size    → GraphicsCommands
  openWindow          : String → (Maybe Point) → ℕ → ℕ
                        → RedrawMode → (Maybe Word32) → GraphicsCommands
  timeGetTime         :                      GraphicsCommands
  drawInWindow        : Window → Graphic → GraphicsCommands
  print               : String →             GraphicsCommands




GraphicsResponses : GraphicsCommands → Set
GraphicsResponses (maybeGetWindowEvent w) = Maybe Event
GraphicsResponses (getWindowEvent w)      = Event
GraphicsResponses (closeWindow w)         = Unit
GraphicsResponses (openWindowNotEx s s')  = Window
GraphicsResponses (openWindow s n1 n2 s' r w) = Window
GraphicsResponses timeGetTime             = Word32
GraphicsResponses _                       = Unit


GraphicsInterface : IOInterface
Command  GraphicsInterface = GraphicsCommands
Response GraphicsInterface = GraphicsResponses

IOGraphics : AgdaSize → Set → Set
IOGraphics i = IO GraphicsInterface i

IOGraphics+ : AgdaSize → Set → Set
IOGraphics+ i = IO+ GraphicsInterface i


translateIOGraphicsLocal : (c : GraphicsCommands) → NativeIO (GraphicsResponses c)
translateIOGraphicsLocal (maybeGetWindowEvent w) = nativeMaybeGetWindowEvent w
translateIOGraphicsLocal (getWindowEvent w)      = nativeGetWindowEvent w
translateIOGraphicsLocal (closeWindow w)         = nativeCloseWindow w
translateIOGraphicsLocal (openWindowNotEx str size)   = nativeOpenWindow str size
translateIOGraphicsLocal (openWindow str point n1 n2 mode word) = nativeOpenWindowExNat str point n1 n2 mode word
translateIOGraphicsLocal timeGetTime             = nativeTimeGetTime
translateIOGraphicsLocal (drawInWindow w g)      = nativeDrawInWindow w g
translateIOGraphicsLocal (print s)             = nativePutStrLn s


translateIOGraphics : {A : Set} → IOGraphics ∞ A → NativeIO A
translateIOGraphics = translateIO translateIOGraphicsLocal
