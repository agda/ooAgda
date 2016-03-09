module SizedPolyIO.ConsoleObject where

open import Size
open import Level using (_⊔_) renaming (suc to lsuc)

open import SizedPolyIO.Console
open import SizedPolyIO.Object
open import SizedPolyIO.IOObject


-- A console object is an IO object for the IO interface  of console
ConsoleObject : ∀{μ ρ}(i : Size)  → (iface : Interface μ ρ) → Set (μ ⊔ ρ)
ConsoleObject i iface = IOObject consoleI iface i

