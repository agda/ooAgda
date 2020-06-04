module examplesPaperJFP.Colists where

-- open import Function

-- Case expressions (to be used with pattern-matching lambdas, see
-- README.Case).

infix 0 case_return_of_ case_of_

case_return_of_ :
  ∀ {a b} {A : Set a}
  (x : A) (B : A → Set b) → ((x : A) → B x) → B x
case x return B of f = f x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = case x return _ of f

data ListF A S : Set where
  nil   :  ListF A S
  cons  :  (a : A) (s : S) → ListF A S

record Colist A : Set where
  coinductive
  field force : ListF A (Colist A)


open Colist using (force)


mapF : ∀{A S S′} (f : S → S′) → (ListF A S → ListF A S′)
mapF f nil         =  nil
mapF f (cons a s)  =  cons a (f s)

-- As an example, we define mapping over potentially infinite lists using
-- copattern matching:

map : ∀{A B} (f : A → B) (l : Colist A) → Colist B
force (map f l) with force l
... | nil        =  nil
... | cons x xs  =  cons (f x) (map f xs)

unfold              :  ∀{A S} (t : S → ListF A S) → (S → Colist A)
force (unfold t s)  with t s
... | nil           =  nil
... | cons a s′     =  cons a (unfold t s′)

fmap : ∀{A B} (f : A → B) (l : Colist A) → Colist B
fmap f = unfold λ l → case force l of λ
  { nil → nil
  ; (cons a s) → cons (f a) s
  }
