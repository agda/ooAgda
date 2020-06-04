{-# OPTIONS --copatterns #-}

module examplesPaperJFP.ExampleDrawingProgram where

open import Size
open import Data.Bool.Base
open import Data.Char.Base
open import Data.Nat.Base hiding (_⊓_; _+_; _*_)
open import Data.List.Base hiding (_++_)
open import Data.Integer.Base hiding (suc)
open import Data.String.Base
open import Data.Maybe.Base
open import Agda.Builtin.Char using (primCharEquality)

open import Function

open import SizedIO.Base
open import SizedIO.IOGraphicsLib hiding (translateIOGraphics)  renaming (translateIOGraphicsLocal to translateNative)

open import NativeInt --PrimTypeHelpers
open import NativeIO

open import examplesPaperJFP.triangleRightOperator

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


mutual

  loop              :  ∀{i} → Window → State → IOGraphics i Unit
  force (loop w s)  =  exec'  (getWindowEvent w) λ e →
                       winEvtHandler w s e

  winEvtHandler : ∀{i} → Window → State → Event → IOGraphics i Unit
  winEvtHandler w s (Key c t)       =  if primCharEquality c 'x'
                                       then (exec (closeWindow w) return)
                                       else loop w s
  winEvtHandler w s (MouseMove p₂)  =  s ▹ λ
                                         { nothing    →  loop w (just p₂)
                                         ; (just p₁)  →  exec (drawInWindow w (line p₁ p₂)) λ _ →
                                                         loop w (just p₂)   }
  winEvtHandler w s _               =  loop w s


program : ∀{i} → IOGraphics i Unit
program =
  exec  (openWindow "Drawing Prog" nothing 1000 1000
      nativeDrawGraphic nothing) λ win →
  loop win nothing

translateIOGraphics : IOGraphics ∞ Unit → NativeIO Unit
translateIOGraphics = translateIO translateNative

main : NativeIO Unit
main = nativeRunGraphics (translateIOGraphics program)
