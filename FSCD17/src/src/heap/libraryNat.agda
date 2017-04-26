module src.heap.libraryNat where

open import Data.Nat renaming (_⊔_ to _⊔n_; _≟_ to _≟ℕ_) hiding ( _<_ )
open import Data.Bool
open import Data.Fin hiding (pred)
open import Data.Unit
open import Data.Empty
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

{-
--- WARNING USES TODO
postulate TODO : {A : Set} → A
-}



_==b_ : ℕ → ℕ → Bool
zero ==b zero = true
zero ==b suc a' = false
suc a ==b zero = false
suc a ==b suc a' = a ==b a'

transferℕ  : (P : ℕ → Set)
            → (a a' : ℕ) → T (a ==b a')
            → P a → P a'
transferℕ P zero zero aa' q = q
transferℕ P zero (suc a') () q
transferℕ P (suc a) zero () q
transferℕ P (suc a) (suc a') aa' q = transferℕ (P ∘ suc) a a' aa' q



_<ℕb_ : ℕ → ℕ → Bool
_ <ℕb zero = false
zero <ℕb suc a' = true
suc a <ℕb suc a' = a <ℕb a'

_<ℕ_ : ℕ → ℕ → Set
n <ℕ m = T (n <ℕb m)

_≦ℕb_ : ℕ → ℕ → Bool
zero ≦ℕb _ = true
suc a ≦ℕb zero = false
suc a ≦ℕb suc a' = a ≦ℕb a'


<ℕb-suc : {a b : ℕ} → T (a <ℕb b) → T (a <ℕb suc b)
<ℕb-suc{zero} = λ _ → tt
<ℕb-suc{_}{zero} ()
<ℕb-suc{suc a}{suc b} = <ℕb-suc{a}{b}

<ℕb-suc' : {a b : ℕ} → T (a ≦ℕb b) → T (a <ℕb suc b)
<ℕb-suc' {zero} {zero} ab = ab
<ℕb-suc' {zero} {suc b} ab = ab
<ℕb-suc' {suc a} {zero} ab = ab
<ℕb-suc' {suc a} {suc b} ab = <ℕb-suc'{a}{b} ab


n<sucnLem : {n m : ℕ} → T  (n ==b m) → T (n <ℕb suc m)
n<sucnLem {zero} {zero} nm = tt
n<sucnLem {zero} {suc m} ()
n<sucnLem {suc n} {zero} ()
n<sucnLem {suc n} {suc m} nm = n<sucnLem {n} {m} nm


n<mImpliesn/=m : (n m : ℕ) → T (m <ℕb n) → ¬ T (n ==b m)
n<mImpliesn/=m zero m ()
n<mImpliesn/=m (suc n) zero p ()
n<mImpliesn/=m (suc n) (suc m) p q = n<mImpliesn/=m n m p q


le : {n m : ℕ} → ¬ (n ==b m) ≡ false → T (n ==b m)
le{zero}{zero} p = tt
le {zero} {suc n} p = p refl
le {suc n} {zero} p = p refl
le {suc n} {suc m} p = le{n}{m} p


refl==b : {n : ℕ} → T (n ==b n)
refl==b {zero} = tt
refl==b {suc n} = refl==b {n}

symb : (n m : ℕ) → T (n ==b m) → T (m ==b n)
symb zero zero p = tt
symb zero (suc m) ()
symb (suc n) zero ()
symb (suc n) (suc m) p = symb n m p


neqsymb : (n m : ℕ) → ¬ T (n ==b m) → ¬ T (m ==b n)
neqsymb n m p q = p (symb m n q)

n<ℕbsucn : {n : ℕ} → T (n <ℕb suc n)
n<ℕbsucn {zero} = tt
n<ℕbsucn {suc n} = n<ℕbsucn{n}

n≦ℕbsucn : {n : ℕ} → T (n ≦ℕb suc n)
n≦ℕbsucn {zero} = tt
n≦ℕbsucn {suc n} = n≦ℕbsucn {n}


¬n<ℕbn : {n : ℕ} → ¬ (T (n <ℕb n))
¬n<ℕbn {zero} ()
¬n<ℕbn {suc n} p = ¬n<ℕbn {n} p

refl≦ℕb : (n : ℕ) → T (n ≦ℕb n)
refl≦ℕb zero = tt
refl≦ℕb (suc n) = refl≦ℕb n

trans≦ℕb : (n m k : ℕ) → T (n ≦ℕb m) → T (m ≦ℕb k) → T (n ≦ℕb k)
trans≦ℕb zero m k nm mk = tt
trans≦ℕb (suc n) zero k () mk
trans≦ℕb (suc n) (suc m) zero nm ()
trans≦ℕb (suc n) (suc m) (suc k) nm mk = trans≦ℕb n m k nm mk



⊔isMaxl : {n m : ℕ} →   T (n ≦ℕb (n ⊔n m ))
⊔isMaxl {zero} {m} = tt
⊔isMaxl {suc n} {zero} = refl≦ℕb (suc n)
⊔isMaxl {suc n} {suc m} = ⊔isMaxl {n} {m}


⊔isMaxr : {n m : ℕ} →   T (m ≦ℕb (n ⊔n m ))
⊔isMaxr {n} {zero}  = tt
⊔isMaxr {zero} {suc m}  = refl≦ℕb (suc m)
⊔isMaxr {suc n} {suc m} = ⊔isMaxr {n} {m}


⊔zero : {n : ℕ} → (n ⊔n zero) ≡ n
⊔zero {zero} = refl
⊔zero {suc n} = refl


⊔isMaxl' : {n m k : ℕ} →   T (n ≦ℕb m ) → T (n ≦ℕb (m ⊔n k ))
⊔isMaxl' {zero} {m} {k} = λ _ → tt
⊔isMaxl' {suc n} {zero} {k} = λ ()
⊔isMaxl' {suc n} {suc m} {zero} = λ z → z
⊔isMaxl' {suc n} {suc m} {suc k} = ⊔isMaxl'{n}{m}


⊔isMax<l : {n m k : ℕ} →   T ((n ⊔n m) <ℕb k) → T (n <ℕb k)
⊔isMax<l {n} {m} {zero} p = p
⊔isMax<l {zero} {m} {suc k} p = tt
⊔isMax<l {suc n} {zero} {suc k} p = p
⊔isMax<l {suc n} {suc m} {suc k} p = ⊔isMax<l {n} {m} {k} p

⊔isMax<r : {n m k : ℕ} →   T ((n ⊔n m) <ℕb k) → T (m <ℕb k)
⊔isMax<r {n} {zero} {zero} p = p
⊔isMax<r {n} {zero} {suc k} p = tt
⊔isMax<r {zero} {suc m} {k} p = p
⊔isMax<r {suc n} {suc m} {zero} p = p
⊔isMax<r {suc n} {suc m} {suc k} p = ⊔isMax<r{n}{m}{k} p

sucinvertible : {n m : ℕ} → suc n ≡ suc m → n ≡ m
sucinvertible {n} {m} = cong pred

¬n≡m→¬sucn≡sucm : {n m : ℕ} → ¬ (n ≡ m) → ¬ (suc n ≡ suc m)
¬n≡m→¬sucn≡sucm {n} {m} p q = p (sucinvertible q)


<impliesnoteq : {n m : ℕ} → T (n  <ℕb m) → ¬ (n ≡ m)
<impliesnoteq {n} {zero} p = λ _ → p
<impliesnoteq {zero} {suc m} p = λ ()
<impliesnoteq {suc n} {suc m} p = ¬n≡m→¬sucn≡sucm {n}{m} (<impliesnoteq{n}{m} p)

<impliesNot= = <impliesnoteq



-- {- Fin n related lemmata -}


-- fromℕ< : ∀ {n m} → n <ℕ m → Fin m
-- fromℕ< {_} {zero} ()
-- fromℕ< {zero} {suc m} p = zero
-- fromℕ< {suc n} {suc m} p = suc (fromℕ< {n} {m} p)


update : {A : Set} (f : ℕ → A) (n : ℕ) (a : A) → ℕ → A
update {A} f n a m = aux  (n ≟ℕ m)
    module updateaux where
           aux : Dec (n ≡ m)
                 →  A
           aux (yes _) = a
           aux (no _) = f m


updateLem : {A : Set}(Q : A → Set)(f : ℕ → A)(n : ℕ)(a : A)
            → (m :  ℕ)
            → ¬ (n ≡ m)
            → Q (f m)
            → Q (update f n a m)
updateLem {A} Q f n a m nm Qfm = aux (n ≟ℕ m)
     module  updateLemaux where
        aux : (x : Dec (n ≡ m)) → Q(updateaux.aux f n a m x)
        aux (yes p) = ⊥-elim (nm p)
        aux (no ¬p) = Qfm


updateLem2 : {A : Set}(f : ℕ → A)(n : ℕ)(a : A)(m : ℕ)
            → (n ≡ m)
            → update f n a m ≡ a
updateLem2 {A} f n a m nm = aux (n ≟ℕ m)
     module  updateLem2aux where
        aux : (x : Dec (n ≡ m)) → updateaux.aux f n a m x ≡ a
        aux (yes p) = refl
        aux (no ¬p) = ⊥-elim (¬p nm)

updateLem3 : {A : Set}(f : ℕ → A)(n : ℕ)(a : A)(m : ℕ)
            → ¬ (n ≡ m)
            → update f n a m ≡ f m
updateLem3 f n a m nm = updateLem (λ a' → a' ≡ f m) f n a m nm refl



leqEmbedLem : (P : ℕ → Set) → (l : (n : ℕ) → P n → P (suc n))
              → (n m : ℕ) → T (n ≦ℕb m) → P n → P m
leqEmbedLem P l zero zero nm p = p
leqEmbedLem P l zero (suc m) nm p = l m (leqEmbedLem P l zero m tt p)
leqEmbedLem P l (suc n) zero () p
leqEmbedLem P l (suc n) (suc m) nm p = leqEmbedLem (P ∘ suc) (l ∘ suc) n m nm p
