{-# OPTIONS --postfix-projections #-}


module examples.heap.correctnessLinkedListProofsAlgebraicLaws where

open import Relation.Binary.PropositionalEquality hiding (sym)

open import Data.Maybe hiding (maybe)

open import src.heap.heapAsObjectBase
open import src.heap.heapAsObjectGeneric

open import Data.Empty renaming (⊥-elim to efq)
open import Data.Fin hiding (lift)

open import Data.Nat hiding (_≟_) renaming (_⊔_ to _⊔n_)
open import Data.Product renaming (proj₁ to pr₁; proj₂ to pr₂; _×_ to _×'_; map to mapp)
open import Data.Unit hiding ( _≟_ )
open import Data.List

open import src.heap.library

open import src.StateSizedIO.RObject renaming (objectMethod to method)
open import examples.heap.correctnessLinkedList

open import src.heap.heapAsObject hiding (readP;writeP)

open heapRObjectFinM

module _ (B : Set)
         (let PointerTypeWP = gLinkedWP B pointerStructfin)
         (let PointerType = PointerTypeWP .El)
         where

  open  moduleHeapDef B
  open heapObjectLLMod B pointerStructfin

  corConsaux : {w : World} → (b : B) → (h : StoreFin PointerTypeWP  w)
            → (p : MPointerfin w)
            → CorrHeapWithPointer (cons b (llist (heapRObject PointerTypeWP h) p))
  corConsaux b h p .theStoreFin = newHfin h (consLLForHead b
                                             (llist (heapRObject (gLinkedWP B pointerStructfin) h) p))
  corConsaux b h p .eqToStoreFin = refl

  corCons : {w : World} → (b : B) → (ll : HeapWithPointer {w})
            → CorrHeapWithPointer ll
            → CorrHeapWithPointer (cons b ll)
  corCons b ll cor  rewrite (cor .eqToStoreFin) = corConsaux b (cor .theStoreFin) (ll .llpoint)



  lemmaConsHead : {w : World} (n : B)(l : HeapWithPointer {w})
                  → CorrHeapWithPointer l
                  → head (cons n l) ≡ just n
  lemmaConsHead n l cor rewrite (cor .eqToStoreFin) = refl




  mutual
     PointsToList : {w : World} (h : HeapObjectLL w)(p : MPointerfin w) →
                    List B → Set
     PointsToList {w} h nothing [] = ⊤
     PointsToList {w} h (just p) [] = ⊥
     PointsToList {w} h p (x ∷ xs) = PointsToListCons h (mreadP h p) x xs

     PointsToListCons : {w : World} (h : HeapObjectLL w)
                        →  Maybe (PointerType w) → B → List B →  Set
     PointsToListCons {w} h nothing x xs = ⊥
     PointsToListCons {w} h (just a) x xs =
                  PointsToListCons2 h x xs (a .getElemLL) (a .getNextLL)

     data PointsToListCons2 {w : World} (h : HeapObjectLL w) : B → List B → B
                                     → MPointerfin w → Set where
       consp : {x : B}{xs : List B}{p : MPointerfin w}
             → PointsToList h p xs
             → PointsToListCons2 {w} h x xs x p


  pointsToListEmptyImliesNothing : {w : World} (h : HeapObjectLL w)(p : MPointerfin w)
                                   (p2list : PointsToList {w} h p [])
                                   → p ≡ nothing
  pointsToListEmptyImliesNothing {w} h (just x) ()
  pointsToListEmptyImliesNothing {w} h nothing p2list = refl

  record IsList {w} (h : HeapObjectLL w) (p : MPointerfin w) : Set where
    constructor isList
    field
       list : List B
       isLcor  : PointsToList h p list

  open IsList public


  PointsToListll : {w : World} (ll : HeapWithPointer {w}) (l : List B) →  Set
  PointsToListll ll l = PointsToList  (ll .llheap) (ll .llpoint) l


  IsListll : {w : World}(ll : HeapWithPointer {w}) → Set
  IsListll {w} ll = IsList {w} (ll .llheap) (ll .llpoint)

  IsListllMaybe : {w : World}(ll : Maybe (HeapWithPointer {w})) → Set
  IsListllMaybe (just x) = IsListll x
  IsListllMaybe nothing = ⊤


  _≡ll_ : {w w' : World} (ll : HeapWithPointer {w}) (ll' : HeapWithPointer {w'}) → Set
  ll ≡ll  ll' = Σ[ l ∈ List B ] (PointsToListll ll l × PointsToListll ll' l)

  _≡llm_ : {w w' : World} (ll : Maybe (HeapWithPointer {w})) (ll' : Maybe (HeapWithPointer {w'})) → Set
  just ll ≡llm  just ll' = ll ≡ll ll'
  nothing ≡llm  nothing = ⊤
  _ ≡llm  _ = ⊥

  nilIsListll : IsListll nill
  nilIsListll .list = []
  nilIsListll .isLcor = tt



  mutual
     lemmaLiftHeapaux2 : { w : World}
                        (newP₁ : LinkedListNodeType B pointerStructfin (suc w))
                        (h : Storeg pointerStructfin (gLinkedWP B pointerStructfin) w)
                        (l : List B)
                        (p : MPointerfin w) -- p will be (↑ h x₁ .getNextLL)
                        (x : PointsToList (heapRObject (gLinkedWP B pointerStructfin) h)
                             p l)
                        → PointsToList
                         (heapRObject (gLinkedWP B pointerStructfin) (newHfin h newP₁))
                         (membedp B pointerStructfin p) l
     lemmaLiftHeapaux2 {w} newP₁ h [] (just x₂) ()
     lemmaLiftHeapaux2 {w} newP₁ h [] nothing x = x
     lemmaLiftHeapaux2 {w} newP₁ h (.(↑ h p .getElemLL) ∷ l) (just p) (consp x) =
             consp (lemmaLiftHeapaux2 newP₁ h l ((↑ h p .getNextLL)) x)

     lemmaLiftHeapaux2 {w} newP₁ h (x₂ ∷ l) nothing ()

     lemmaLiftHeapaux : {w : World}
                     → (newP : PointerType (suc w))
                     → (h : StoreFin PointerTypeWP  w)
                     → (p : MPointerfin w)
                     → (l : List B)
                     → PointsToList (heapRObject PointerTypeWP h) p l
                     → PointsToList (nextH newP (heapRObject PointerTypeWP  h)) (membedp B pointerStructfin p) l

     lemmaLiftHeapaux {w} newP₁ h (just x) [] ()
     lemmaLiftHeapaux {w} newP₁ h nothing [] q = q
     lemmaLiftHeapaux {w} newP₁ h (just x₁) (.(↑ h x₁ .getElemLL) ∷ l) (consp x) =
                 consp (lemmaLiftHeapaux2 newP₁ h l (↑ h x₁ .getNextLL) x)
     lemmaLiftHeapaux {w} newP₁ h nothing (x ∷ l) ()


     lemmaLiftHeap : {w : World}
                     → (newP : PointerType (suc w))
                     → (h : HeapObjectLL w)
                     → HeapCorrect h
                     → (p : MPointerfin w)
                     → (l : List B)
                     → PointsToList h p l
                     → PointsToList (nextH newP h) (membedp B pointerStructfin p) l
     lemmaLiftHeap {w} newP h cor nothing [] x = x
     lemmaLiftHeap {w} newP h cor (just p) [] ()
     lemmaLiftHeap {w} newP h cor nothing (x' ∷ xs) ()
     lemmaLiftHeap {w} newP h cor (just p) (x' ∷ l) x rewrite (cor .eqToStoreFin) = lemmaLiftHeapaux {w} newP (cor .theStoreFin) (just p) (x' ∷ l) x



     lemmaLiftHeapCons : {w : World}
                     → (newP : PointerType (suc w))
                     → (h : HeapObjectLL w)
                     → HeapCorrect h
                     → (q : Maybe (PointerType w))
                     → (x : B)
                     → (xs : List B)
                     → PointsToListCons h q x xs
                     → PointsToListCons (nextH newP h)
                                         (liftMLL B pointerStructfin {w} q) x xs

     lemmaLiftHeapCons {w} newP h hcor (just o) x xs x₁ =
            lemmaLiftHeapCons2 newP h hcor o x xs x₁
     lemmaLiftHeapCons {w} newP h hcor nothing x xs ()

     lemmaLiftHeapCons2 : {w : World}
                     → (newP : PointerType (suc w))
                     → (h : HeapObjectLL w)
                     → HeapCorrect h
                     → (a : LinkedListNodeType B pointerStructfin w )
                     → (x : B)
                     → (xs : List B)
                     → PointsToListCons2 h x xs (a .getElemLL) (a .getNextLL)
                     → PointsToListCons2 (nextH newP h) x xs
                            (getElemLL (liftLL B pointerStructfin {w} a))
                            (getNextLL (liftLL B pointerStructfin {w} a))
     lemmaLiftHeapCons2 newP₁ h hcor a .(a .getElemLL) [] (consp x) rewrite (pointsToListEmptyImliesNothing h (a .getNextLL) x) = consp _
     lemmaLiftHeapCons2 newP₁ h hcor a .(a .getElemLL) (x₁ ∷ xs) (consp x) rewrite (hcor .eqToStoreFin) =
            consp (lemmaLiftHeapaux2 newP₁ (hcor .theStoreFin) (x₁ ∷ xs) (a .getNextLL) x)





  lemmaCons1aux : ∀ {w}
                  {h' : StoreFin PointerTypeWP  w} {p : Fin w} {l : List B} {b : B} →
                  (pt : Maybe (Fin w))
                  (p2l : PointsToList
                        (heapRObject (gLinkedWP B pointerStructfin) h')
                        (pt) l)
                  → PointsToList
                  (heapRObject (gLinkedWP B pointerStructfin)
                    (newHfin h' (linkedListNode b (just (suc p)))))
                  (membedp B pointerStructfin (pt)) l

  lemmaCons1aux {w} {h'} {p} {[]} {b} (just x) ()
  lemmaCons1aux {w} {h'} {p} {.(↑ h' x .getElemLL) ∷ l} {b} (just x) (consp x₁) =
    consp (lemmaCons1aux {w}{h'}{_} {l} {b} (↑ h' x .getNextLL) x₁)


  lemmaCons1aux {w} {h'} {p} {[]} {b} nothing p2l = _
  lemmaCons1aux {w} {h'} {p} {x ∷ l} {b} nothing ()




  lemmaCons1 : {w : World}
               → (h : HeapObjectLL w)
               → HeapCorrect h
               → (p : MPointerfin w)
               → (l : List B)
               → PointsToList h p l
               → (b : B)
               → PointsToList (consHeapUnpack b h p)
                              (just (consNewUnpack b h p ))
                              (b ∷ l)
  lemmaCons1 h cor nothing [] pl b rewrite (cor .eqToStoreFin) = consp _
  lemmaCons1 h cor nothing (x ∷ l) () b
  lemmaCons1 h cor (just p) [] () b
  lemmaCons1 h cor (just p) (.(h .readerMethod (readPh p) .getElemLL) ∷ l) (consp x) b rewrite (cor .eqToStoreFin) =
            consp (consp (lemmaCons1aux (↑ (cor .theStoreFin) p .getNextLL) x))







  lemmaCons2 : {w : World}
               → (ll : HeapWithPointer {w})
               → (cor : CorrHeapWithPointer ll)
               → (l : List B)
               → PointsToListll ll l
               → (n : B)
               → PointsToListll (cons n ll) (n ∷ l)
  lemmaCons2 ll cor l lll n = lemmaCons1 (ll .llheap) cor (ll .llpoint) l lll n


  tailLem'' : {w : World} → (h : HeapObjectLL w)
           → (p : Maybe (PointerType w))
           → (n : B) → (l : List B)
           → PointsToListCons h p n l
           → Σ[ ll' ∈ HeapWithPointer {w} ]
               ((tailaux h p ≡ just ll') × (PointsToListll ll' l))
  tailLem'' {w} h (just o) .(getElemLL o) l (consp x) = llist h (o. getNextLL ) , (refl ,, x)
  tailLem'' {w} h nothing n l ()



  tailLem' : {w : World} → (h : HeapObjectLL w)
           → (p : MPointerfin w)
           → (n : B) → (l : List B)
           → PointsToList h p (n ∷ l)
           → Σ[ ll' ∈ HeapWithPointer {w} ]
               ((tail' h p ≡ just ll') × (PointsToListll ll' l))
  tailLem' h (just p) n l x = tailLem'' h (just (readP h p)) n l x
  tailLem' h nothing n l ()


  tailLem : {w : World} → (ll : HeapWithPointer {w} )
           → (n : B) → (l : List B)
           → PointsToListll ll (n ∷ l)
           → Σ[ ll' ∈ HeapWithPointer {w} ]
               ((tail ll ≡ just ll') × (PointsToListll ll' l))
  tailLem {w} ll n l p = tailLem' (ll .llheap) (ll .llpoint) n l p


  lemmaCons' : {w : World}
               → (ll : HeapWithPointer {w})
               → (cor : CorrHeapWithPointer ll)
               → (l : List B)
               → IsListll ll
               → (n : B)
               → Σ[ ll' ∈ HeapWithPointer {sucw w} ]
                  ((tail (cons n ll) ≡ just ll') ×  (ll  ≡ll ll'))
  lemmaCons' {w} ll cor l x n = let
                                   h : HeapObjectLL w
                                   h = ll .llheap

                                   p : MPointerfin w
                                   p = ll .llpoint

                                   l : List B
                                   l = x .list

                                   pl : PointsToList h p l
                                   pl = x .isLcor

                                   cor' : HeapCorrect h
                                   cor' = cor

                                   q : PointsToList (consHeapUnpack n h p) (just (consNew n (llist h p ))) (n ∷ l)
                                   q = lemmaCons1 h cor' p l pl n

                                   q' : PointsToListll (cons n ll) (n ∷ l)
                                   q' = q

                                   q'' : Σ[ ll' ∈ HeapWithPointer {sucw w} ]
                                         ((tail (cons n  ll) ≡ just ll') ×
                                        (PointsToListll ll' l))
                                   q'' = tailLem (cons n ll) n l q'

                                   ll'' : HeapWithPointer {sucw w}
                                   ll'' = pr₁ q''

                                   q3 : tail (cons n  ll) ≡ just ll''
                                   q3 = proj₁ (pr₂ q'')

                                   q4 : PointsToListll ll'' l
                                   q4 = proj₂ (pr₂ q'')

                           in ll'' , (q3 ,, (l , (pl ,, q4)))



  lemmaCons : {w : World}
               → (ll : HeapWithPointer {w})
               → (cor : CorrHeapWithPointer ll)
               → (l : List B)
               → IsListll ll
               → (n : B)
               → tail (cons n ll) ≡llm just ll
  lemmaCons {w} ll cor l x n = let
                                   h : HeapObjectLL w
                                   h = ll .llheap

                                   p : MPointerfin w
                                   p = ll .llpoint

                                   l : List B
                                   l = x .list

                                   pl : PointsToList h p l
                                   pl = x .isLcor

                                   cor' : HeapCorrect h
                                   cor' = cor

                                   q : PointsToList (consHeapUnpack n h p) (just (consNew n (llist h p ))) (n ∷ l)
                                   q = lemmaCons1 h cor' p l pl n

                                   q' : PointsToListll (cons n ll) (n ∷ l)
                                   q' = q

                                   q'' : Σ[ ll' ∈ HeapWithPointer {sucw w} ]
                                         ((tail (cons n  ll) ≡ just ll') ×
                                        (PointsToListll ll' l))
                                   q'' = tailLem (cons n ll) n l q'

                                   ll'' : HeapWithPointer {sucw w}
                                   ll'' = pr₁ q''

                                   q3 : just ll'' ≡ tail (cons n  ll)
                                   q3 = sym (proj₁ (pr₂ q''))

                                   q4 : PointsToListll ll'' l
                                   q4 = proj₂ (pr₂ q'')

                                   q5 : ll'' ≡ll ll
                                   q5 = l , (q4 ,, pl)

                                   q6 : just ll'' ≡llm just ll
                                   q6 = q5

                           in subst (λ x₁ → x₁ ≡llm just ll) q3 q6



  lemmaConsIsList : {w : World}
               → (ll : HeapWithPointer {w})
               → (cor : CorrHeapWithPointer ll)
               → (l : List B)
               → IsListll ll
               → (n : B)
               → IsListll (cons n ll)
  lemmaConsIsList {w} ll cor l x n = let
                                   h : HeapObjectLL w
                                   h = ll .llheap

                                   p : MPointerfin w
                                   p = ll .llpoint

                                   l : List B
                                   l = x .list

                                   pl : PointsToList h p l
                                   pl = x .isLcor

                                   cor' : HeapCorrect h
                                   cor' = cor

                                   q : PointsToList (consHeapUnpack n h p) (just (consNew n (llist h p ))) (n ∷ l)
                                   q = lemmaCons1 h cor' p l pl n

                                   q' : PointsToListll (cons n ll) (n ∷ l)
                                   q' = q
                                      in isList (n ∷ l) q'


  tailLem4 : {w : World} → (ll : HeapWithPointer {w} )
           → PointsToListll ll []
           → nothing ≡ tail ll
  tailLem4 {w} ll x rewrite (pointsToListEmptyImliesNothing (ll .llheap) (ll .llpoint) x) = refl



  tailIsListll : {w : World} (ll : HeapWithPointer {w})
                 → IsListll ll
                 → IsListllMaybe (tail ll)
  tailIsListll ll (isList [] isLcor) = let
                                                               q : nothing ≡ tail ll
                                                               q = tailLem4 ll isLcor
                                                           in subst (λ x → IsListllMaybe x) q tt
  tailIsListll ll (isList (x ∷ xs) isLcor) = let
                                                 t : Σ[ ll' ∈ HeapWithPointer ]
                                                     ((tail ll ≡ just ll') × PointsToListll ll' xs)
                                                 t = tailLem ll x xs isLcor

                                                 ll' : HeapWithPointer
                                                 ll' = pr₁ t

                                                 lltail : just ll' ≡ tail ll
                                                 lltail = sym (proj₁ (pr₂ t))

                                                 llpoints : PointsToListll ll' xs
                                                 llpoints = proj₂ (pr₂ t)
                                             in subst (λ y → IsListllMaybe y) lltail (isList xs llpoints)
