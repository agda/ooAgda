module StateSizedIO.GUI.WxGraphicsLib where

open import SizedIO.Base
open import StateSizedIO.GUI.BaseStateDependent 

open import Size renaming (Size to AgdaSize)

open import Data.Bool.Base
open import Data.List.Base

open import Function

open import NativeIO

open import StateSizedIO.GUI.WxBindingsFFI  
open import StateSizedIO.GUI.VariableList



data GuiLev1Command : Set where
  makeFrame         : GuiLev1Command
  makeButton        : Frame   → GuiLev1Command
  addButton         : Frame   → Button → GuiLev1Command
  drawBitmap        : DC      → Bitmap → Point → Bool → GuiLev1Command
  repaint           : Frame   → GuiLev1Command

GuiLev1Response : GuiLev1Command → Set
GuiLev1Response makeFrame           = Frame
GuiLev1Response (makeButton _)      = Button
GuiLev1Response _                   = Unit

GuiLev1Interface : IOInterface 
Command   GuiLev1Interface = GuiLev1Command
Response  GuiLev1Interface = GuiLev1Response



GuiLev2State : Set₁
GuiLev2State = VarList

data GuiLev2Command (s :  GuiLev2State) : Set₁ where 
  level1C           : GuiLev1Command → GuiLev2Command s
  createVar         : {A : Set} → A → GuiLev2Command s
  setButtonHandler  : Button → List (prod s → IO GuiLev1Interface ∞ (prod s))
                      → GuiLev2Command s
  setKeyHandler     : Button
                      → List (prod s → IO GuiLev1Interface ∞ (prod s))
                      → List (prod s → IO GuiLev1Interface ∞ (prod s))
                      → List (prod s → IO GuiLev1Interface ∞ (prod s))
                      → List (prod s → IO GuiLev1Interface ∞ (prod s))
                      → GuiLev2Command s                      
  setOnPaint        : Frame
                     → List (prod s → DC → Rect → IO GuiLev1Interface ∞ (prod s)) 
                     → GuiLev2Command s

GuiLev2Response : (s : GuiLev2State) → GuiLev2Command s → Set
GuiLev2Response _ (level1C c)         = GuiLev1Response c
GuiLev2Response _ (createVar {A} a)   = Var A
GuiLev2Response _ _                   = Unit

GuiLev2Next : (s : GuiLev2State) → (c : GuiLev2Command s) 
              → GuiLev2Response s c
              → GuiLev2State
GuiLev2Next s (createVar {A} a) var = addVar A var s
GuiLev2Next s _  _                  = s

GuiLev2Interface : IOInterfaceˢ
Stateˢ     GuiLev2Interface = GuiLev2State
Commandˢ   GuiLev2Interface = GuiLev2Command
Responseˢ  GuiLev2Interface = GuiLev2Response
nextˢ      GuiLev2Interface = GuiLev2Next

translateLev1Local : (c : GuiLev1Command) → NativeIO (GuiLev1Response c)
translateLev1Local makeFrame              = nativeMakeFrame
translateLev1Local (makeButton fra)       = nativeMakeButton fra
translateLev1Local (addButton fra bt)     = nativeAddButton fra bt
translateLev1Local (drawBitmap dc bm p b) = nativeDrawBitmap dc bm p b
translateLev1Local (repaint fra)          = nativeRepaint fra

translateLev1 : {A : Set} → IO GuiLev1Interface ∞ A → NativeIO A
translateLev1 = translateIO translateLev1Local

translateLev1List : {A : Set} → List (IO GuiLev1Interface ∞ A) → List (NativeIO A)
translateLev1List l = map translateLev1 l




translateLev2Local : (s : GuiLev2State)
                          → (c : GuiLev2Command s) 
                          → NativeIO (GuiLev2Response s c)
translateLev2Local s (level1C c) = translateLev1Local c
                           
translateLev2Local s (createVar {A} a)   = nativeNewVar {A} a
translateLev2Local s (setButtonHandler bt proglist)  
    = nativeSetButtonHandler bt 
            (dispatchList s (map (λ prog → translateLev1 ∘ prog)  proglist))

translateLev2Local s (setKeyHandler bt proglistRight proglistLeft proglistUp proglistDown)  
    =  nativeSetKeyHandler bt
           (λ key -> case (showKey key) of λ
                 { "Right" → (dispatchList s (map (λ prog → translateLev1 ∘ prog)  proglistRight))
                 ; "Left" → (dispatchList s (map (λ prog → translateLev1 ∘ prog)  proglistLeft))
                 ; "Up" → (dispatchList s (map (λ prog → translateLev1 ∘ prog)  proglistUp)) 
                 ; "Down" → (dispatchList s (map (λ prog → translateLev1 ∘ prog)  proglistDown)) 
                 ; _  → nativeReturn unit
                 } )



translateLev2Local s (setOnPaint fra proglist)  
    = nativeSetOnPaint fra (λ dc rect → (dispatchList s 
         (map (λ prog aa → translateLev1 (prog aa dc rect)) proglist)))


translateLev2 : {s : GuiLev2State} → {A : Set} 
                     → IOˢ GuiLev2Interface ∞ (λ _ → A) s → NativeIO A
translateLev2 = translateIOˢ {I = GuiLev2Interface} translateLev2Local
  

