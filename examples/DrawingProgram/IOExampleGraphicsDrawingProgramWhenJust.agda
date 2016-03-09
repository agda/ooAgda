{-# OPTIONS --copatterns #-}

module IOExampleGraphicsDrawingProgramWhenJust where


open import Data.Bool.Base
open import Data.Char.Base renaming (primCharEquality to charEquality)
open import Data.Nat.Base hiding (_≟_;_⊓_; _+_; _*_)
open import Data.List.Base hiding (_++_)
open import Data.Integer.Base hiding (suc)
open import Data.String.Base
open import Data.Maybe.Base

open import Function

open import SizedIO.Base
open import SizedIO.IOGraphicsLib

open import NativeInt --PrimTypeHelpers
open import NativeIO

integerLess     :  ℤ →  ℤ → Bool
integerLess x y with ∣(y - (x ⊓ y))∣
... | zero = true
... | z = false

line : Point → Point → Graphic
line p  newpoint = withColor red (polygon
                       (point x y
                        ∷ point a b
                        ∷ point (a + xAddition) (b + yAddition)
                        ∷ point (x + xAddition) (y + yAddition)
                        ∷ [] ) )
  where
  x = proj1Point p
  y = proj2Point p
  a = proj1Point newpoint
  b = proj2Point newpoint

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
  λ{  (Key c t)      →  if charEquality c 'x' then return _ else loop w s
   ;  (MouseMove p₂) →  whenJust s (λ p₁ → do1 (drawInWindow w (line p₁ p₂))) >>= λ _ →
                        loop w (just p₂)
   ; _               →  loop w  s
   }

myProgram : ∀{i} → IOGraphics i Unit
myProgram =
  do (openWindow "Drawing Program" nothing
       (just (size (+ 1000) (+ 1000))) nativeDrawGraphic nothing) λ window →
  loop window nothing


main : NativeIO Unit
main = nativeRunGraphics (translateIOGraphics myProgram)
