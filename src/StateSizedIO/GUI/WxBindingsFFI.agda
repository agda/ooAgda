module StateSizedIO.GUI.WxBindingsFFI where

open import Data.Bool.Base
open import Data.Integer
open import Data.Nat

open import Data.Product hiding (map)

open import NativeIO



{-# FOREIGN GHC import qualified GHC.Conc.Sync #-}
{-# FOREIGN GHC import qualified Control.Concurrent #-}
{-# FOREIGN GHC import qualified Control.Concurrent.STM.TVar #-}


{-# FOREIGN GHC import qualified Data.IORef #-}

{-# FOREIGN GHC import qualified Graphics.UI.WX #-}
{-# FOREIGN GHC import qualified Graphics.UI.WX.Timer #-}
{-# FOREIGN GHC import qualified Graphics.UI.WXCore #-}
{-# FOREIGN GHC import qualified Graphics.UI.WXCore.Events #-}





postulate Frame : Set
{-# COMPILE GHC Frame = type (Graphics.UI.WX.Frame ()) #-}



postulate Button : Set
{-# COMPILE GHC Button = type (Graphics.UI.WX.Button ()) #-}

postulate TextCtrl : Set
{-# COMPILE GHC TextCtrl = type (Graphics.UI.WX.TextCtrl ()) #-}

postulate Timer : Set
{-# COMPILE GHC Timer = type Graphics.UI.WX.Timer.Timer #-}


postulate nativeNewFrame : String -> NativeIO Frame
{-# COMPILE GHC nativeNewFrame = (\s -> Graphics.UI.WX.frame [Graphics.UI.WX.text Graphics.UI.WX.:= "Window"]) #-}


--
-- Frame Layout
--
{-# FOREIGN GHC
setChildrenLayout' ::   Graphics.UI.WX.Frame () -> Integer -> Integer -> Integer -> Integer -> IO ()
setChildrenLayout' win rowWidth' marginWidth' vspa' hspa' = exec

  let rowWidth = fromIntegral rowWidth'
  let marginWidth = fromIntegral marginWidth'
  let vspa = fromIntegral vspa'
  let hspa = fromIntegral hspa'

  let list2Matrix n xs = map (\(x ,y)-> (take n) $ (drop (n*x)) y) $ zip [0..] $ replicate (div (length xs)  n) xs

  blist <- Graphics.UI.WXCore.windowChildren win
  putStrLn ("Layout of frame, got " ++ (show $ length $ blist) ++ "children")

  let  blist' = list2Matrix rowWidth blist
  let  blist'' = (map . map) Graphics.UI.WX.widget blist'

  Graphics.UI.WX.set win [ Graphics.UI.WX.layout Graphics.UI.WX.:= Graphics.UI.WX.margin marginWidth $ Graphics.UI.WX.dynamic $ Graphics.UI.WX.grid vspa hspa $ blist'']



#-}



postulate nativeSetChildredLayout : Frame → ℕ → ℕ → ℕ → ℕ → NativeIO Unit
{-# COMPILE GHC nativeSetChildredLayout = setChildrenLayout' #-}

postulate nativeDoThreadDelay : NativeIO Bool
{-# COMPILE GHC nativeDoThreadDelay = ((Control.Concurrent.threadDelay 100) >>= (\x -> return True)) #-}


postulate nativeSetIdle : Frame -> NativeIO Bool -> NativeIO Unit
{-# COMPILE GHC nativeSetIdle = (\fra prog -> Graphics.UI.WX.set fra [Graphics.UI.WX.on Graphics.UI.WX.idle Graphics.UI.WX.:= prog]) #-}


nativeCreateFrame : NativeIO Frame
nativeCreateFrame =
  nativeNewFrame "Start Text" native>>= (\f ->
  nativeSetIdle f nativeDoThreadDelay native>>= (\x ->
  nativeReturn f))

postulate nativeMakeButton : Frame → String → NativeIO Button
{-# COMPILE GHC nativeMakeButton = (\myFrame str -> Graphics.UI.WX.button myFrame [Graphics.UI.WX.text Graphics.UI.WX.:= (Data.Text.unpack str)]) #-}

postulate nativeMakeTextCtrl : Frame  → String → NativeIO TextCtrl
{-# COMPILE GHC nativeMakeTextCtrl = (\myFrame str -> Graphics.UI.WX.entry myFrame [Graphics.UI.WX.text Graphics.UI.WX.:= (Data.Text.unpack str)]) #-}

postulate nativeAddButton : Frame → Button → NativeIO Unit
{-# COMPILE GHC nativeAddButton = (\myFrame bt -> Graphics.UI.WX.set myFrame [Graphics.UI.WX.layout Graphics.UI.WX.:= Graphics.UI.WX.minsize (Graphics.UI.WX.sz 500 400) $ Graphics.UI.WX.column 1 [Graphics.UI.WX.hfill (Graphics.UI.WX.widget bt)]]) #-}



postulate WxColor : Set
{-# COMPILE GHC WxColor = type Graphics.UI.WX.Color #-}

postulate nativeSetColorButton : Button → WxColor → NativeIO Unit
{-# COMPILE GHC  nativeSetColorButton = (\ bt co -> Graphics.UI.WX.set bt [ Graphics.UI.WX.color Graphics.UI.WX.:= co] ) #-}

postulate nativeSetColorTextCtrl : TextCtrl → WxColor → NativeIO Unit
{-# COMPILE GHC  nativeSetColorTextCtrl = (\ txt co -> Graphics.UI.WX.set txt [ Graphics.UI.WX.color Graphics.UI.WX.:= co] ) #-}

postulate nativeGetTextFromTxtBox : TextCtrl → NativeIO String
{-# COMPILE GHC  nativeGetTextFromTxtBox = (\ txt -> (Graphics.UI.WX.get txt Graphics.UI.WX.text) >>= (\s -> return (Data.Text.pack s))) #-}

postulate rgb : ℕ → ℕ → ℕ → WxColor
{-# COMPILE GHC rgb = (\ r b g -> Graphics.UI.WX.rgb r g b) #-}


postulate  TVar : Set → Set
{-# COMPILE GHC TVar = type Control.Concurrent.STM.TVar.TVar #-}

postulate  MVar : Set → Set
{-# COMPILE GHC MVar = type Control.Concurrent.MVar #-}

Var : Set → Set
Var = MVar



postulate
  nativeNewVar : {A : Set} → A → NativeIO (Var A)
  nativeTakeVar : {A : Set} → Var A → NativeIO A
  nativePutVar : {A : Set} → Var A → A → NativeIO Unit

{-# COMPILE GHC nativeNewVar = (\ _ -> Control.Concurrent.newMVar ) #-}
{-# COMPILE GHC nativeTakeVar = (\ _ -> Control.Concurrent.takeMVar ) #-}
{-# COMPILE GHC nativePutVar = (\ _ -> Control.Concurrent.putMVar ) #-}



-- Fire Custom Event
--
postulate nativeFireCustomEvent : Frame → NativeIO Unit
{-# COMPILE GHC nativeFireCustomEvent = (\f -> Graphics.UI.WXCore.commandEventCreate Graphics.UI.WXCore.wxEVT_COMMAND_MENU_SELECTED (Graphics.UI.WXCore.wxID_HIGHEST+1) >>= (\ev -> fmap (\x -> ()) (Graphics.UI.WXCore.evtHandlerProcessEvent f ev))) #-}



postulate nativeRegisterCustomEvent : Frame → NativeIO Unit → NativeIO Unit
{-# COMPILE GHC nativeRegisterCustomEvent = (\win prog -> Graphics.UI.WXCore.evtHandlerOnMenuCommand win (Graphics.UI.WXCore.wxID_HIGHEST+1) (putStrLn " >>> CUSTOM EVENT FIRED <<<" >> Control.Concurrent.forkIO prog >> return ())) #-}


{-
for debugging
postulate nativeRegisterDummyCustomEvent : Frame → NativeIO Unit
{-# COMPILE GHC nativeRegisterDummyCustomEvent = (\win -> Graphics.UI.WXCore.evtHandlerOnMenuCommand win (Graphics.UI.WXCore.wxID_HIGHEST+1) (putStrLn " >>> CUSTOM EVENT FIRED <<<")) #-}
-}

postulate nativeSetButtonHandler : Button → NativeIO Unit → NativeIO Unit
{-# COMPILE GHC nativeSetButtonHandler = (\ bt prog -> Graphics.UI.WX.set bt [Graphics.UI.WX.on Graphics.UI.WX.command Graphics.UI.WX.:= prog ]) #-}

postulate prog : NativeIO Unit
{-# COMPILE GHC prog = (putStrLn "timer goes off!") #-}

postulate nativeSetTimer : Frame → ℤ → NativeIO Unit → NativeIO Timer
{-# COMPILE GHC nativeSetTimer = (\ fra x prog -> Graphics.UI.WX.timer fra [ Graphics.UI.WX.interval Graphics.UI.WX.:= (fromInteger x) , Graphics.UI.WX.on Graphics.UI.WX.command Graphics.UI.WX.:= prog ]) #-}

postulate ThreadId : Set
{-# COMPILE GHC ThreadId = type GHC.Conc.Sync.ThreadId #-}

postulate forkIO : NativeIO Unit → NativeIO ThreadId
{-# COMPILE GHC forkIO = GHC.Conc.Sync.forkIO #-}

postulate Bitmap : Set
{-# COMPILE GHC Bitmap = type (Graphics.UI.WXCore.Bitmap ())  #-}

postulate bitmap : String → Bitmap
{-# COMPILE GHC bitmap = (\s -> Graphics.UI.WX.bitmap (Data.Text.unpack s)) #-}

postulate DC : Set
{-# COMPILE GHC DC = type (Graphics.UI.WXCore.DC ()) #-}

postulate Rect : Set
{-# COMPILE GHC Rect = type Graphics.UI.WXCore.Rect #-}

postulate nativeSetClickRight : Frame  → NativeIO Unit → NativeIO Unit
{-# COMPILE GHC nativeSetClickRight = (\ fra prog -> Graphics.UI.WX.set fra [Graphics.UI.WX.on Graphics.UI.WX.clickRight Graphics.UI.WX.:= (\x -> prog)]) #-}


postulate nativeSetOnPaint : Frame → (DC → Rect → NativeIO Unit) → NativeIO Unit
{-# COMPILE GHC nativeSetOnPaint = (\ fra prog -> Graphics.UI.WX.set fra [Graphics.UI.WX.on Graphics.UI.WX.paint Graphics.UI.WX.:= prog]) #-}

postulate nativeRepaint : Frame → NativeIO Unit
{-# COMPILE GHC nativeRepaint = Graphics.UI.WX.repaint #-}

Point : Set
Point = (ℤ × ℤ)

postulate NativePoint : Set
{-# COMPILE GHC NativePoint = type Graphics.UI.WXCore.Point #-}

postulate nativePoint : ℤ → ℤ → NativePoint
{-# COMPILE GHC nativePoint = (\ x y -> Graphics.UI.WXCore.point (fromInteger x) (fromInteger y)) #-}


postulate nativeDrawBitmapNativePoint : DC → Bitmap → NativePoint → Bool → NativeIO Unit
{-# COMPILE GHC nativeDrawBitmapNativePoint = (\ d bi p bo -> Graphics.UI.WX.drawBitmap d bi p bo [] ) #-}


nativeDrawBitmap : DC → Bitmap → Point → Bool → NativeIO Unit
nativeDrawBitmap d bi (x , y) bo = nativeDrawBitmapNativePoint d bi (nativePoint x y) bo

{-# FOREIGN GHC import Graphics.UI.WXCore.WxcClassesAL #-}

postulate nativeBitmapGetWidth : Bitmap → NativeIO ℤ
{-# COMPILE GHC nativeBitmapGetWidth = (\ b -> fmap fromIntegral (Graphics.UI.WXCore.WxcClassesAL.bitmapGetWidth b)) #-}

postulate start : NativeIO Unit → NativeIO Unit
{-# COMPILE GHC start = Graphics.UI.WX.start #-}

--
--  Note: we add the "key pressed" event to a button
--  and not to a frame, because of a bug in wxHaskell that prevents
--  adding a key pressed event to a frame (at least on linux plattforms).
--


postulate
  Key : Set
  showKey : Key -> String
  nativeSetKeyHandler : Button → (Key → NativeIO Unit) → NativeIO Unit

{-# COMPILE GHC Key = type Graphics.UI.WXCore.Events.Key #-}
{-# COMPILE GHC showKey = (\ k -> (Data.Text.pack (Graphics.UI.WXCore.Events.showKey k))) #-}

{-# COMPILE GHC nativeSetKeyHandler = (\bt prog -> Graphics.UI.WX.set bt [Graphics.UI.WX.on Graphics.UI.WX.anyKey Graphics.UI.WX.:= prog]) #-}



--
-- Delete Objects
--

-- note: can be solved with instance arguments in the future
postulate objectDeleteFrame : Frame → NativeIO Unit
{-# COMPILE GHC objectDeleteFrame = (\f -> Graphics.UI.WX.objectDelete f) #-}

postulate nativeDeleteButton : Button → NativeIO Unit
{-# COMPILE GHC nativeDeleteButton = (\f -> Graphics.UI.WX.objectDelete f) #-}

postulate nativeDeleteTextCtrl : TextCtrl → NativeIO Unit
{-# COMPILE GHC nativeDeleteTextCtrl = (\f -> Graphics.UI.WX.objectDelete f) #-}
