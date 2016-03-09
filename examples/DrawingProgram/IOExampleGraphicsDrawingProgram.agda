{-# OPTIONS --copatterns #-}

module IOExampleGraphicsDrawingProgram where


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
  λ{  (Key c t)      →  if charEquality c 'x' then (do (closeWindow w) return) 
                                              else loop w s
   ;  (MouseMove p₂) →  case s of
      λ{ nothing     →  loop w (just p₂)
       ; (just p₁)   →  do (drawInWindow w (line p₁ p₂)) λ _ →
                        loop w (just p₂)
       }
   ; _               →  loop w  s
   }


{-
loop                 :  ∀{i} → Window → State → IOGraphics i Unit
force (loop w s)     =  do'  (getWindowEvent w)
  λ{  (Key c t)      →  if charEquality c 'x' then return _ else loop w s
   ;  (MouseMove p₂) →  case s of
      λ{ nothing     →  loop w (just p₂)
       ; (just p₁)   →  do (drawInWindow w (line p₁ p₂)) λ _ →
                        loop w (just p₂)
       }
   ; _               →  loop w  s
   }
-}

{-
mutual 
  loop                 :  ∀{i} → Window → State → IOGraphics i Unit
  force (loop w s)     =  do'  (getWindowEvent w)  (λ e → aux w e s)

  aux                  :  ∀{i} → Window → Event → State → IOGraphics i Unit
  aux w (Key c t) s              = if charEquality c 'x' then (do (closeWindow w) λ _ → return _)
                                   else loop w s
  aux w (MouseMove p₂) (just p₁) = do (drawInWindow w (line p₁ p₂)) (λ _ → 
                                   loop w (just p₂))
  aux w (MouseMove p₂) nothing   = loop w (just p₂)
  aux w _  s                     = loop w s
-}

{-
tailrecursion discussion

mutual 
  loop                 :  ∀{i} → Window → State → IOGraphics i Unit
  command (force (loop w s))     =  (getWindowEvent w)  
  response (force (loop w s)) e    = aux w e s

  aux                  :  ∀{i} → Window → Event → State → IOGraphics i Unit
  command (aux w (MouseMove p₂) (just p₁)) = (drawInWindow w (line p₁ p₂)) 
  response (aux w (MouseMove p₂) (just p₁)) _ = loop w (just p₂))
  aux w (MouseMove p₂) nothing   = loop w (just p₂)
  aux w _  s                     = loop w s

-}


{-
  λ{  (Key c t)      →  if charEquality c 'x' then
                          (do ? λ _ → return _) else loop w s
   ;  (MouseMove p₂) →  case s of
      λ{ nothing     →  loop w (just p₂)
       ; (just p₁)   →  do (drawInWindow w (line p₁ p₂)) λ _ →
                        loop w (just p₂)
       }
   ; _               →  loop w  s
   }
-}



myProgram : ∀{i} → IOGraphics i Unit
myProgram =
  do (openWindow "Drawing Program" nothing
       (just (size (+ 1000) (+ 1000))) nativeDrawGraphic nothing) λ window →
  loop window nothing
 

main : NativeIO Unit
main = nativeRunGraphics (translateIOGraphics myProgram)
