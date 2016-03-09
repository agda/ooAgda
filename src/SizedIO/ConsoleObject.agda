module SizedIO.ConsoleObject where

open import Size

open import SizedIO.Console
open import SizedIO.Object
open import SizedIO.IOObject


-- A console object is an IO object for the IO interface  of console
ConsoleObject : (i : Size)  → (iface : Interface) → Set
ConsoleObject i iface = IOObject consoleI iface i

