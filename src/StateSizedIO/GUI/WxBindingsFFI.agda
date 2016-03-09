module StateSizedIO.GUI.WxBindingsFFI where

open import Data.Bool.Base
open import Data.Integer

open import Data.Product hiding (map)

open import NativeIO
open import NativeInt

open import Function

{-# IMPORT GHC.Conc.Sync #-}
{-# IMPORT Control.Concurrent #-}
{-# IMPORT Graphics.UI.WX #-}
{-# IMPORT Graphics.UI.WXCore #-}
{-# IMPORT Graphics.UI.WXCore.Events #-}

postulate Frame : Set
{-# COMPILED_TYPE Frame (Graphics.UI.WX.Frame ()) #-}

postulate Button : Set
{-# COMPILED_TYPE Button (Graphics.UI.WX.Button ()) #-}


postulate nativeNewFrame : String -> NativeIO Frame
{-# COMPILED nativeNewFrame (\s -> Graphics.UI.WX.frame
  [Graphics.UI.WX.text Graphics.UI.WX.:= (Data.Text.unpack s)]) #-}

postulate nativeDoThreadDelay : NativeIO Bool
{-# COMPILED nativeDoThreadDelay ((Control.Concurrent.threadDelay 100) >>= (\x -> return True)) #-}

postulate nativeSetIdle : Frame -> NativeIO Bool -> NativeIO Unit
{-# COMPILED nativeSetIdle (\fra prog -> Graphics.UI.WX.set fra
  [Graphics.UI.WX.on Graphics.UI.WX.idle Graphics.UI.WX.:= prog]) #-}

nativeMakeFrame : NativeIO Frame
nativeMakeFrame =
  nativeNewFrame "Start Text" native>>= (\f -> 
  nativeSetIdle f nativeDoThreadDelay native>>= (\x ->
  nativeReturn f))   

postulate nativeMakeButton : Frame → NativeIO Button
{-# COMPILED nativeMakeButton (\myFrame -> Graphics.UI.WX.button myFrame
  [Graphics.UI.WX.text Graphics.UI.WX.:= "click"]) #-}

postulate nativeAddButton : Frame → Button → NativeIO Unit
{-# COMPILED nativeAddButton (\myFrame bt -> Graphics.UI.WX.set myFrame
  [Graphics.UI.WX.layout Graphics.UI.WX.:=
    Graphics.UI.WX.minsize (Graphics.UI.WX.sz 500 400) $
      Graphics.UI.WX.column 1 [Graphics.UI.WX.hfill (Graphics.UI.WX.widget bt)]]) #-}


postulate  TVar : Set → Set
{-# COMPILED_TYPE TVar Control.Concurrent.STM.TVar.TVar  #-}

postulate  MVar : Set → Set
{-# COMPILED_TYPE MVar Control.Concurrent.MVar  #-}

Var : Set → Set
Var = MVar


postulate
  nativeNewVar : {A : Set} → A → NativeIO (Var A)
  nativeTakeVar : {A : Set} → Var A → NativeIO A
  nativePutVar : {A : Set} → Var A → A → NativeIO Unit

{-# COMPILED nativeNewVar (\ _ -> Control.Concurrent.newMVar ) #-}
{-# COMPILED nativeTakeVar (\ _ -> Control.Concurrent.takeMVar ) #-}
{-# COMPILED nativePutVar (\ _ -> Control.Concurrent.putMVar ) #-}


postulate nativeSetButtonHandler : Button → NativeIO Unit → NativeIO Unit
{-# COMPILED nativeSetButtonHandler (\ bt prog -> Graphics.UI.WX.set bt
  [Graphics.UI.WX.on Graphics.UI.WX.command Graphics.UI.WX.:= prog ]) #-}

postulate ThreadId : Set
{-# COMPILED_TYPE ThreadId GHC.Conc.Sync.ThreadId #-}

postulate forkIO : NativeIO Unit → NativeIO ThreadId
{-# COMPILED forkIO GHC.Conc.Sync.forkIO #-}


postulate Bitmap : Set
{-# COMPILED_TYPE Bitmap (Graphics.UI.WXCore.Bitmap ()) #-}

postulate bitmap : String → Bitmap
{-# COMPILED bitmap (\s -> Graphics.UI.WX.bitmap (Data.Text.unpack s))  #-}

postulate DC : Set
{-# COMPILED_TYPE DC (Graphics.UI.WXCore.DC ()) #-}

postulate Rect : Set
{-# COMPILED_TYPE Rect Graphics.UI.WXCore.Rect #-}


postulate nativeSetOnPaint : Frame → (DC → Rect → NativeIO Unit) → NativeIO Unit
{-# COMPILED nativeSetOnPaint (\ fra prog -> Graphics.UI.WX.set fra [Graphics.UI.WX.on Graphics.UI.WX.paint Graphics.UI.WX.:= prog]) #-}

postulate nativeRepaint : Frame → NativeIO Unit
{-# COMPILED nativeRepaint Graphics.UI.WX.repaint #-}


Point : Set
Point = (ℤ × ℤ)

postulate NativePoint : Set
{-# COMPILED_TYPE NativePoint Graphics.UI.WXCore.Point #-}

postulate nativePoint : ℤ → ℤ → NativePoint
{-# COMPILED nativePoint (\ x y -> Graphics.UI.WXCore.point (fromInteger x) (fromInteger y)) #-}


postulate nativeDrawBitmapNativePoint : DC → Bitmap → NativePoint → Bool → NativeIO Unit
{-# COMPILED nativeDrawBitmapNativePoint (\ d bi p bo -> Graphics.UI.WX.drawBitmap d bi p bo [] ) #-}

nativeDrawBitmap : DC → Bitmap → Point → Bool → NativeIO Unit
nativeDrawBitmap d bi (x , y) bo = nativeDrawBitmapNativePoint d bi (nativePoint x y) bo


postulate start : NativeIO Unit → NativeIO Unit
{-# COMPILED start Graphics.UI.WX.start #-}


--
--  Note: we add the "key pressed" event to a button
--  and not to a frame, because of a bug in wxHaskell that prevents
--  adding a key pressed event to a frame (at least on linux plattforms).
--


postulate
  Key : Set
  showKey : Key -> String
  nativeSetKeyHandler : Button → (Key → NativeIO Unit) → NativeIO Unit

{-# COMPILED_TYPE Key Graphics.UI.WXCore.Events.Key #-}
{-# COMPILED showKey (\ k -> (Data.Text.pack (Graphics.UI.WXCore.Events.showKey k))) #-}

{-# COMPILED nativeSetKeyHandler (\bt prog -> Graphics.UI.WX.set bt [Graphics.UI.WX.on Graphics.UI.WX.anyKey Graphics.UI.WX.:= prog]) #-}

