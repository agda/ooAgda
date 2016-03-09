module SizedIO.coIOIO where

open import Size


mutual
  data coIO²  (i : Size) (j : Size)
              (Cin : Set ) (Rin : Cin  → Set)
              (Cext : Set) (Rext : Cext → Set)
              (A : Set) : Set where
     return : A → coIO² i j Cin Rin Cext Rext A
     dof    : (i' : Size< i) →
              (c : Cin) → (Rin c → coIO² i' j Cin Rin Cext Rext A)
              → coIO² i j Cin Rin Cext Rext A
     do∞    : (c : Cext)
              → (Rext c → coIO²∞ j Cin Rin Cext Rext A)
              → coIO² i j Cin Rin Cext Rext A

  record coIO²∞ (j : Size) (Cin : Set ) (Rin : Cin  → Set)
                            (Cext : Set) (Rext : Cext → Set)
                            (A : Set) : Set where
    coinductive
    field
      force : (j' : Size< j)
               → coIO² ∞ j' Cin Rin Cext Rext A

open coIO²∞ public
