module examplesPaperJFP.Sized where

open import Data.Product using (_×_; _,_)
open import Data.String

open import Function using (case_of_)
open import Size

open import examplesPaperJFP.NativeIOSafe
open import examplesPaperJFP.BasicIO using (IOInterface; Command; Response)
open import examplesPaperJFP.ConsoleInterface
open import examplesPaperJFP.Console using (translateIOConsoleLocal)
open import examplesPaperJFP.Object using (Interface; Method; Result;
  cellJ; CellMethod; get; put; CellResult)


module UnfoldF where
  open import examplesPaperJFP.Coalgebra using (F; mapF)
  record νF (i : Size) : Set where
    coinductive
    constructor delay
    field force : ∀(j : Size< i) → F (νF j)

  open νF using (force)

  unfoldF : ∀{S} (t : S → F S) → ∀ i → (S → νF i)
  force (unfoldF t i s) j = mapF (unfoldF t j) (t s)

mutual
  record IO (Iᵢₒ : IOInterface) (i : Size)  (A : Set) : Set where
    coinductive

    constructor delay
    field force : {j : Size< i} → IO′ Iᵢₒ j A

  data IO′ (Iᵢₒ : IOInterface) (i : Size)  (A : Set) : Set where
    exec′      :  (c : Command Iᵢₒ) (f : Response Iᵢₒ c → IO Iᵢₒ i A)  → IO′ Iᵢₒ i A
    return′  :  (a : A)                                              → IO′ Iᵢₒ i A

module NestedRecursion (Iᵢₒ : IOInterface) (A : Set) where

  data F (X : Set) : Set where
    exec′      :  (c : Command Iᵢₒ) (f : Response Iᵢₒ c → X)  → F X
    return′  :  (a : A)                                     → F X

  record νF (i : Size) : Set where
    coinductive
    constructor delay
    field force : {j : Size< i} → F (νF j)

open IO public

module _  {Iᵢₒ : IOInterface } (let C = Command Iᵢₒ) (let R = Response Iᵢₒ) where

  infixl 2 _>>=_

  exec      :  ∀ {i A}    (c : C) (f : R c → IO Iᵢₒ i A) → IO Iᵢₒ i A
  return  :  ∀ {i A}    (a : A) → IO Iᵢₒ i A
  _>>=_   :  ∀ {i A B}  (m : IO Iᵢₒ i A) (k : A → IO Iᵢₒ i B) → IO Iᵢₒ i B

  force (exec c f)    = exec′ c f
  force (return a)  =  return′ a

  force (_>>=_ {i} m k) {j} with force m {j}
  ... | exec′ c f     =  exec′ c λ r → _>>=_ {j} (f r) k
  ... | return′ a   =  force (k a) {j}


  {-# NON_TERMINATING #-}
  translateIO : ∀{A : Set}
    →  (translateLocal : (c : C) → NativeIO (R c))
    →  IO Iᵢₒ ∞ A
    →  NativeIO A
  translateIO translateLocal m = case (force m) of
    λ{ (exec′ c f)    → (translateLocal c) native>>= λ r →
         translateIO translateLocal (f r)
     ; (return′ a) → nativeReturn a
     }

record IOObject (Iᵢₒ : IOInterface) (I : Interface) (i : Size) : Set where
  coinductive
  field method  :  ∀{j : Size< i} (m : Method I)
                   → IO Iᵢₒ ∞ (Result I m × IOObject Iᵢₒ I j)


open IOObject public


CellC : (i : Size) → Set
CellC = IOObject ConsoleInterface (cellJ String)

simpleCell : ∀{i} (s : String) → CellC i
force (method (simpleCell {i} s) {j} get) =
  exec′ (putStrLn ("getting (" ++ s ++ ")")) λ _ →
  return (s , simpleCell {j} s)
force (method (simpleCell _) (put s)) =
  exec′ (putStrLn ("putting (" ++ s ++ ")")) λ _ →
  return (unit , simpleCell s)

program : ∀{i} → IO ConsoleInterface i Unit
force program =
  let c₁ = simpleCell "Start" in
  exec′ getLine          λ{ nothing → return unit; (just s) →
  method c₁ (put s)    >>= λ{ (_ , c₂) →
  method c₂ get        >>= λ{ (s′ , c₃) →
  exec (putStrLn s′)     λ _ →
  program }}}


main : NativeIO Unit
main = translateIO translateIOConsoleLocal program
