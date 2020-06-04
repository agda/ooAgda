{-# OPTIONS --copatterns #-}

module IOExampleGraphicsMovingText where

--
--  not yet updated for new SizedIO library
--  not yet updated to change with IOInterface Record of Commands / Responses
--

{-

open import SizedIO.General
open import SizedIO.IOGraphicsLib -- TODO

open import Data.Bool.Base
open import Data.Char.Base
open import Data.Nat.Base
open import Data.List.Base hiding (_++_)
open import Data.Integer.Base hiding (_+_;suc)
open import Data.String.Base
open import Data.Maybe.Base

open import Function
open import Size

width :  ℕ
width = 125

height :  ℕ
height = 20

myBox : Point  → Graphic
myBox p  = withColor black (polygon  ( point x y
                                      ∷ point (x +IntNat width) y
                                      ∷ point (x +IntNat width) (y +IntNat height)
                                      ∷ point x (y +IntNat height)
                                      ∷ [] ) )
               where x = proj1Point p
                     y = proj2Point p

record State : Set where
  constructor state
  field oldpoint : Maybe Point
        newpoint : Maybe Point
open State


module _ (w : Window) where

  -- If there was a mouse movement since the last invokation of refresh
  -- overwrite old text and place text at new mouse position.
  refresh : ∀{i} → State → IOGraphics i State
  refresh s =  case newpoint s of
    λ{ nothing → return s
     ; (just lastMousePoint) →
         {- case there was a new mouse movement. -}
         (whenJust (oldpoint s) λ p →
              exec1 (drawInWindow w (myBox p)) >>
              exec1 (drawInWindow w (withColor white (text lastMousePoint ("1st :some Text")))))
           >> return (state (just lastMousePoint) nothing)
     }

  processEvent : ∀{i} → State → IOGraphics+ i (Maybe State)
  processEvent s =
    exec (getWindowEvent w)
      λ{ {- key event: check whether this was equal to 'x'; if yes, terminate, otherwise return to loop -}
         (Key c t) →
           if (c ==CharBool 'x') then return nothing else return (just s)

         {- mouse event: if this was the first ever event, ignore it, but
             record that the next mouse event is no longer the first one.
            If it was not the first ever event: set newpoint to the position of the mouse p -}
       ; (MouseMove p) →
           return (just record s{ newpoint = just p })

         {- otherwise just go back to start -}
       ; _ →
           return (just s)
       }

  loop : ∀{i} → State → IOGraphics i Unit
  force (loop s) = processEvent s >>=+'  -- maybe′ loop (return _)
    λ{ nothing   → return _
     ; (just s') → refresh s' >>= loop
     }

myProgram : ∀{i} → IOGraphics i Unit
force myProgram =
  exec   (openWindowEx "Hello World" nothing (just (natSize 1000 1000)) nativeDrawGraphic nothing) λ window →
  loop window (state nothing nothing)

main : NativeIO Unit
main = nativeRunGraphics (translateIOGraphics myProgram)
-}
