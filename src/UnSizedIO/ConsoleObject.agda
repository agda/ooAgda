module UnSizedIO.ConsoleObject where

open import UnSizedIO.Console
open import UnSizedIO.Object
open import UnSizedIO.IOObject

-- A console object is an IO object for the IO interface  of console
ConsoleObject : (iface : Interface) → Set
ConsoleObject iface = IOObject ConsoleInterface iface



