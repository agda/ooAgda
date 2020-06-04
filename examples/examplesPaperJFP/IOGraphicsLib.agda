{-# OPTIONS --copatterns #-}

module examplesPaperJFP.IOGraphicsLib where


open import Data.Bool.Base
open import Data.Char.Base
open import Data.Nat.Base hiding (_⊓_; _+_; _*_)
open import Data.List.Base hiding (_++_)
open import Data.Integer.Base hiding (suc)
open import Data.String.Base
open import Data.Maybe.Base

open import Function

open import Size

open import SizedIO.Base
open import SizedIO.IOGraphicsLib hiding (GraphicsCommands; GraphicsResponses; GraphicsInterface; IOGraphics) renaming (Size to WindowSize)

open import NativeInt --PrimTypeHelpers
open import NativeIO



data GraphicsCommands  :  Set where
  getWindowEvent  :  Window  →  GraphicsCommands
  openWindow      :  String  →  Maybe Point  →  ℕ  → ℕ
                             →  RedrawMode   →  Maybe Word32
                             →  GraphicsCommands
  closeWindow     :  Window  →  GraphicsCommands
  drawInWindow    :  Window  →  Graphic → GraphicsCommands


GraphicsResponses  :                       GraphicsCommands → Set
GraphicsResponses  (getWindowEvent _)        =  Event
GraphicsResponses  (openWindow _ _ _ _ _ _)  =  Window
GraphicsResponses  (closeWindow _)           =  Unit
GraphicsResponses  (drawInWindow _ _)        =  Unit

GraphicsInterface            :  IOInterface
Command   GraphicsInterface  =  GraphicsCommands
Response  GraphicsInterface  =  GraphicsResponses

IOGraphics : Size → Set → Set
IOGraphics i = IO GraphicsInterface i


translateNative : (c : GraphicsCommands) → NativeIO (GraphicsResponses c)

translateNative  (getWindowEvent w)               =  nativeGetWindowEvent w
translateNative  (openWindow str point n1 n2 m w)  =  nativeOpenWindowExNat str point n1 n2 m w
translateNative  (closeWindow w)                  =  nativeCloseWindow w
translateNative  (drawInWindow w g)               =  nativeDrawInWindow w g
