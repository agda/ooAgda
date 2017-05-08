--@PREFIX@correctnessLinkedList
{-# OPTIONS --postfix-projections #-}

module examples.heap.correctnessLinkedListSessionTypes where

open import Relation.Binary.PropositionalEquality hiding (sym)

open import Data.String renaming (_==_ to _==Str_)

open import Data.Maybe hiding (maybe)

open import Size hiding (↑_)
open import Data.Sum

open import src.SizedIO.Base
open import src.NativeIO

open import src.heap.heapAsObjectBase
open import src.heap.heapAsObjectGeneric

open import src.StateSizedIO.writingOOsUsingIOReaderMethods hiding (nˢ)

open import src.SizedIO.Console using (putStrLn; getLine; consoleI; translateIOConsoleLocal)

open import Data.Bool.Base
open import Data.Empty renaming (⊥-elim to efq)

open import Data.Product renaming (proj₁ to pr₁; proj₂ to pr₂; _×_ to _×'_; map to mapp)
open import Data.Unit hiding ( _≟_ )
open import Data.List

open import examples.heap.correctnessLinkedList
open import examples.heap.correctnessLinkedListStep2
open import examples.heap.correctnessLinkedListProofsAlgebraicLaws
open import src.heap.heapAsObject
open import examples.heap.correctnessLinkedListExampleProg

open heapRObjectFinM
open heapObjectLLMod
open moduleHeapDef


--@BEGIN@SessionCommands
data sessionCommands (B : Set) : Set  where
  putB      : (b : B) → sessionCommands B
  assumeB assumeCmd putError : sessionCommands B
--@END

--@BEGIN@SessionResponses
sessionResponse  : (B : Set) (sC : sessionCommands B) → Set
sessionResponse B assumeB    =  B
sessionResponse B assumeCmd  =  StackCmd
sessionResponse _ _          =  Unit
--@END

--@BEGIN@SessionInterface
sessionInterface : (B : Set) → IOInterface
sessionInterface B .Command   =  sessionCommands B
sessionInterface B .Response  =  sessionResponse B
--@END

--@BEGIN@SessionIO
sessionIO  : {i : Size}(A : Set) → Set
sessionIO  {i} A = IO (sessionInterface String) i A
--@END

--@BEGIN@SessionIOprime
sessionIO'  : {i : Size}(A : Set) → Set
sessionIO'  {i} A = IO' (sessionInterface String) i A
--@END

--@BEGIN@stringIsErrorString
stringIsErrorString : String → Bool
stringIsErrorString str = (str ==Str "got nothing") ∨  (str ==Str "Error -  Stack is empty") ∨
                          (str ==Str "Please enter top, pop, or push")
--@END

--@BEGIN@programsSpecialisedToFinx
finStrWP : WorldPred
finStrWP = gLinkedWP String pointerStructfin

LLStrfin : World → Set
LLStrfin = StoreFin finStrWP

HeapObjectStrfin : {w : World} (h : LLStrfin w)
                   → HeapRObjectfin finStrWP w
HeapObjectStrfin  = heapRObject finStrWP


PointsToListStrLL : {w : World}(h : LLStrfin w)(mp : MPointerfin w)(l : List String) → Set
PointsToListStrLL {w} h mp l = PointsToList  String {w} (HeapObjectStrfin h) mp l
--@END

mutual

--@BEGIN@sessionProg
    sessionProg : {i : Size}(l : List String) → sessionIO {i} Unit
    sessionProg l .force {j} = sessionProg+ l
--@END


--@BEGIN@sessionProgPlus
--@C    -- sessionProg+ reads a command from the console.
    sessionProg+ : {i : Size}(l : List String) → sessionIO' {i} Unit
    sessionProg+ l =  do' assumeCmd (sessionProgStep2 l)

    sessionProgStep2 : {i : Size}(l : List String)(cmd : StackCmd) → sessionIO {i} Unit
    sessionProgStep2 l cmd .force = sessionProgStep2+ l cmd


--@C    sessionProgStep2 interprets the command  as a cmd and makes case distinction on it.
    sessionProgStep2+ : {i : Size}(l : List String)(cmd : StackCmd) → sessionIO' {i} Unit
--@C
--@C    in case the command is top: one prints the top element; in case emptystack put error
--@C
    sessionProgStep2+ []         top   =  do' putError λ _ → sessionProg []
    sessionProgStep2+ (str ∷ l)  top   =  do' (putB str) λ _ →  sessionProg (str ∷ l)
--@END
    -- Push: read an element from the console and put it onto the stack.

    sessionProgStep2+ l          push  =  do' assumeB λ str → sessionProg (str ∷ l)

    -- Pop: pop an element from the stack; in case emptystack put error
--@BEGIN@sessionProgPop
    sessionProgStep2+ []         pop  =  do' putError λ _ →   sessionProg []
    sessionProgStep2+ (_ ∷ l)    pop  =  sessionProg+ l
--@END

    -- Undefcmd: any other command
--@BEGIN@sessionProgUndef
    sessionProgStep2+ l undefcmd      =   do' putError λ _ →  sessionProg l

--@END

--@BEGIN@existsPointL
data existsPointL (w : World)(h : LLStrfin  w)
                  (Rest : (mp : MPointerfin w) (l : List String)
                          (pointstolist : PointsToListStrLL h mp l) → Set) : Set where
       existsPointLC : (mp : MPointerfin w)(l : List String)
                       (pointstolist : PointsToListStrLL h mp l)
                       (rest : Rest mp l pointstolist)  → existsPointL w h Rest
--@END



mutual
--@BEGIN@SimPlusType
   Sim+ : (i : Size) (w : World)
          (p : IOˢindcoind+ ConsoleInterfaceˢ (HeapInterfaceˢIO Pointerfin finStrWP) ∞
                      (λ _ _ → Unit) _ w)
          (h : LLStrfin  w) (mp : MPointerfin w) (l : List String)
          (pointstolist : PointsToListStrLL h mp l)
          (q : IO' (sessionInterface String) ∞ Unit) → Set
--@END
--@BEGIN@SimPlusDef
   Sim+ i w (doˢIO (putStrLn x) f) h point l pointstolist (do' (putB str) g) =
           x ≡ str ×' Sim∞ i w  (f _) h point l pointstolist (g _)
--@C
   Sim+ i w (doˢIO (putStrLn x) f) h point l pointstolist (do' putError g) =
           T ( stringIsErrorString x) ×' Sim∞ i w  (f _) h point l pointstolist (g _)
--@C
   Sim+ i w (doˢobj (inj₁ (newPh x)) f) h point l pointstolist q =
           existsPointL (sucw w) (newHfin h x)    λ mp l' pointstolist →
           Sim+ i (sucw w) (f newfin) (newHfin h x) mp l' pointstolist q
--@END

   Sim+ i w (doˢIO getLine f) h point l pointstolist (do' assumeB g) =
           (str : String) →   Sim∞ i w (f str) h point l pointstolist (g str)
--@C
   Sim+ i w (doˢIO getLine f) h point l pointstolist (do' assumeCmd g) =
           (str : String) →   Sim∞ i w (f str) h point l pointstolist (g (str2StackCmd str))
--@C
   Sim+ i w (doˢobj (inj₁ (writePh p el)) f) h point l pointstolist q =
           existsPointL w (writeHfin h p el)      λ mp l' pointstolist →
           Sim+ i w (f _) (writeHfin h p el) mp l' pointstolist q
--@C
   Sim+ i w (doˢobj (inj₂ (readPh p)) f) h point l pointstolist q =
           existsPointL w h                      λ mp l' pointstolist →
           Sim+ i w (f (↑ h p)) h mp l' pointstolist q
--@C
   Sim+ i w (returnˢic x) h point l pointstolist (return' a) = Unit
--@C
   Sim+ i w _ _ _ _ _ _ = ⊥

--@BEGIN@SimInfty
   record Sim∞  (i : Size)(w : World)
                       (p : IOˢindcoind ConsoleInterfaceˢ (HeapInterfaceˢIO Pointerfin finStrWP) ∞
                            (λ _ _ → Unit) _ w)
                       (h : LLStrfin  w)
                       (mp : MPointerfin w)
                       (l : List String)
                       (pointtolist : PointsToListStrLL h mp l)
                       (q : IO (sessionInterface String) ∞ Unit) : Set where
      coinductive
      field
        forceSim : {j : Size< i} →
                   Sim+ j w (p .forceIC) h mp l pointtolist (q .force)
--@END

open Sim∞


mutual
--@BEGIN@corExampleProg
  corExampleProg : {i : Size}{w : World}(mp : MPointerfin w) (h : LLStrfin  w)(l : List String)
                   (pointstolist : PointsToListStrLL h mp l)
                   → Sim∞ i w (exampleProg pointerStructfin mp) h mp  l pointstolist (sessionProg {∞} l)

  corExampleProg mp h l pointstolist .forceSim str .forceSim =
            corExampleProgStep2 (str2StackCmd str) mp h l pointstolist
--@END


--@BEGIN@corExampleProgStepTwo
  corExampleProgStep2 : {i : Size}{w : World}(cmd : StackCmd) (mp : MPointerfin w)
                        (h : LLStrfin  w)  (l : List String) (pointstolist : PointsToListStrLL h mp l)
                       → Sim+ i w  (exampleProgStep2+ pointerStructfin mp cmd) h mp  l pointstolist
                                    (sessionProgStep2+ l cmd)  --@HIDE-BEG
--@C
  corExampleProgStep2 push (just x) h [] () str
  corExampleProgStep2 push (just x) h (str' ∷ l) pointstolist str .forceSim =
     existsPointLC (just newfin) (str ∷ str' ∷ l)
    (lemmaCons2 String (llist _ _) (corHeapObjectLL String h) (str' ∷ l) pointstolist str) (λ str'' →
              corExampleProgStep2∞ (str2StackCmd str'') (just newfin)
                (newHfin h (linkedListNode str (membedp String pointerStructfin (just x))))
                (str ∷ str' ∷ l)
                (lemmaCons2 String (llist _ _) (corHeapObjectLL String h) (str' ∷ l) pointstolist str))
  corExampleProgStep2 push nothing h [] _ str .forceSim =
      existsPointLC (just newfin) (str ∷ []) (consp _) λ str' →
      corExampleProgStep2∞ (str2StackCmd str') (just newfin)
       (newHfin h (linkedListNode str (membedp String pointerStructfin nothing))) (str ∷ []) (consp tt)
  corExampleProgStep2 push nothing h (x ∷ l) () str
--@HIDE-END
--@C
  corExampleProgStep2 top (just x) h [] ()
  corExampleProgStep2 top (just x) h (.(↑ h x .getElemLL) ∷ l) (consp pointstolist) =
               existsPointLC (just x) ((↑ h x .getElemLL) ∷ l) (consp pointstolist) (refl ,
                             corExampleProg (just x) h (↑ h x .getElemLL ∷ l) (consp pointstolist))
  corExampleProgStep2 top nothing h [] pointstolist = _ , corExampleProg nothing h [] pointstolist
  corExampleProgStep2 top nothing h (x ∷ l) ()
--@END

  corExampleProgStep2 pop (just x) h [] ()
  corExampleProgStep2 pop nothing h [] pointstolist = _ , corExampleProg nothing h [] tt
  corExampleProgStep2 pop (just p) h (.(↑ h p .getElemLL) ∷ l) (consp pointstolist)
             = existsPointLC (↑ h p .getNextLL) l pointstolist λ str →
                corExampleProgStep2∞ (str2StackCmd str) (↑ h p .getNextLL) h l pointstolist
  corExampleProgStep2 pop nothing h (x ∷ l) ()


  corExampleProgStep2 undefcmd mp h [] pointstolist = _ , corExampleProg mp h [] pointstolist --
  corExampleProgStep2 undefcmd mp h (str ∷ l) pointstolist = _ , corExampleProg mp h (str ∷ l) pointstolist


--@BEGIN@corExampleProgStepTwoInfty
  corExampleProgStep2∞ : {i : Size}{w : World}(cmd : StackCmd)(mp : MPointerfin w) (h : LLStrfin  w)
                         (l : List String)
                         (pointstolist : PointsToListStrLL h mp l)
                         → Sim∞ i w (exampleProgStep2 pointerStructfin mp cmd)
                           h mp  l pointstolist   (sessionProgStep2 l cmd)

  corExampleProgStep2∞ cmd mp h l pointstolist .forceSim =
           corExampleProgStep2 cmd mp h l pointstolist
--@END


--@BEGIN@corExampleProgMain
corExampleProgMain : Sim∞ ∞ ∅w (exampleProg pointerStructfin nothing)  ∅Hfin nothing
                     [] tt (sessionProg {∞} [])
corExampleProgMain = corExampleProg nothing ∅Hfin [] _
--@END

-- We define a simulation which works for arbitrary return types (not just Unit type)
-- and  demands a relation R for the return types

mutual
--@BEGIN@SimPlusFull
   SimFull+ : (i : Size)(A : Unit → World → Set)(A' : Set)
          (R : (w : World)(a : A _ w)(h : LLStrfin  w)
               (mp : MPointerfin w)(l : List String)
               (pointstolist : PointsToListStrLL h mp l)
               (a' : A') → Set)
          (w : World)
          (p : IOˢindcoind+ ConsoleInterfaceˢ (HeapInterfaceˢIO Pointerfin finStrWP) ∞ A _ w)
          (h : LLStrfin  w)
          (mp : MPointerfin w)
          (l : List String)
          (pointstolist : PointsToListStrLL h mp l)
          (q : IO' (sessionInterface String) ∞ A')
          → Set
   SimFull+ i A A' R w (doˢIO (putStrLn x) f) h point l pointstolist (do' (putB str) g) =
           x ≡ str ×' SimFull∞ i A A' R w  (f _) h point l pointstolist (g _)
   SimFull+ i A A' R w (doˢIO (putStrLn x) f) h point l pointstolist (do' putError g) =
           T ( stringIsErrorString x) ×' SimFull∞ i A A' R w  (f _) h point l pointstolist (g _)
   SimFull+ i A A' R w (doˢIO getLine f) h point l pointstolist (do' assumeB g) =
           (str : String) →   SimFull∞ i A A' R w (f str) h point l pointstolist (g str)
   SimFull+ i A A' R w (doˢIO getLine f) h point l pointstolist (do' assumeCmd g) =
           (str : String) →   SimFull∞ i A A' R w (f str) h point l pointstolist (g (str2StackCmd str))
   SimFull+ i A A' R w (doˢobj (inj₁ (newPh x)) f) h point l pointstolist q =
           existsPointL (sucw w) (newHfin h x)    λ mp l' pointstolist →
           SimFull+ i A A' R (sucw w) (f newfin) (newHfin h x) mp l' pointstolist q
   SimFull+ i A A' R w (doˢobj (inj₁ (writePh p el)) f) h point l pointstolist q =
           existsPointL w (writeHfin h p el)      λ mp l' pointstolist →
           SimFull+ i A A' R w (f _) (writeHfin h p el) mp l' pointstolist q
   SimFull+ i A A' R w (doˢobj (inj₂ (readPh p)) f) h point l pointstolist q =
           existsPointL w h                      λ mp l' pointstolist →
           SimFull+ i A A' R w (f (↑ h p)) h mp l' pointstolist q
   SimFull+ i A A' R w (returnˢic x) h point l pointstolist (return' a) =
           R w x h point l pointstolist a
   SimFull+ i A A' R w _ _ _ _ _ _ = ⊥
--@END



--@BEGIN@SimFullInfty
   record SimFull∞  (i : Size)(A : Unit → World → Set) (A' : Set)
                (R : (w : World)(a : A _ w)
                    (h : LLStrfin  w)
                    (mp : MPointerfin w)
                    (l : List String)
                    (pointstolist : PointsToListStrLL h mp l)
                    (a' : A') → Set)
                (w : World)
                (p : IOˢindcoind ConsoleInterfaceˢ (HeapInterfaceˢIO Pointerfin finStrWP) ∞ A _ w)
                (h : LLStrfin  w)
                (mp : MPointerfin w)
                (l : List String)
                (pointtolist : PointsToListStrLL h mp l)
                (q : IO (sessionInterface String) ∞ A') : Set where
      coinductive
      field
        forceSimFull : {j : Size< i} →
                   SimFull+ j A A' R w (p .forceIC) h mp l pointtolist (q .force)
--@END

open SimFull∞


UnitReturn : (u : Unit)(w : World) → Set
UnitReturn _ _ = Unit

TrivialRel : (w : World)(a : UnitReturn _ w) (h : LLStrfin  w)
             (mp : MPointerfin w) (l : List String)
              (pointstolist : PointsToListStrLL h mp l)
              (_ : Unit) → Set
TrivialRel _ _ _ _ _ _  _ = Unit

SimTrivialReturn+ : (i : Size) (w : World)
                   (p : IOˢindcoind+ ConsoleInterfaceˢ (HeapInterfaceˢIO Pointerfin finStrWP) ∞ UnitReturn _ w)
                   (h : LLStrfin  w)
                   (mp : MPointerfin w)
                   (l : List String)
                   (pointstolist : PointsToListStrLL h mp l)
                   (q : IO' (sessionInterface String) ∞ Unit) → Set
--@BEGIN@SimTrivial
SimTrivialReturn+ i w p h mp l pointstolist q =
         Sim+ i w p h mp  l pointstolist q
--@END


SimTrivialReturn∞ : (i : Size) (w : World)
                   (p : IOˢindcoind ConsoleInterfaceˢ (HeapInterfaceˢIO Pointerfin finStrWP) ∞ UnitReturn _ w)
                   (h : LLStrfin  w)
                   (mp : MPointerfin w)
                   (l : List String)
                   (pointstolist : PointsToListStrLL h mp l)
                   (q : IO (sessionInterface String) ∞ Unit) → Set
--@BEGIN@SimTrivialInfty
SimTrivialReturn∞ i w p h mp l pointstolist q = Sim∞ i w p h mp  l pointstolist q
--@END


emptySessionProg : sessionIO {∞} Unit
emptySessionProg = return _

emptySessionProg+ : sessionIO' {∞} Unit
emptySessionProg+ = return' _

consHeapRelation : (w : World)
                   (lold : List String)
                   (str : String)
                   (w' : World)
                   (a : w' ≡ sucw w  ×' Pointerfin w')
                   (h : LLStrfin  w')
                   (mp : MPointerfin w')
                   (lnew : List String)
                   (pointstolist : PointsToListStrLL h mp lnew)
                   (a' : Unit) → Set
consHeapRelation w lold str w' a h mp lnew pointstolist q' = mp ≡ just (pr₂ a) ×' (lnew ≡ str ∷ lold)


bisimProofCons : {w : World} (str : String)(mp : MPointerfin w) (lold : List String)
                 (h : LLStrfin  w)
                 (pointstolist : PointsToListStrLL h mp lold)
                 → SimFull+ ∞ (λ _ w' → w' ≡ sucw w  ×' Pointerfin w') Unit
                           (consHeapRelation w lold str)
                           w (consHeapProgIndCoind+ pointerStructfin String {w} str mp)
                           h mp lold pointstolist emptySessionProg+
bisimProofCons {w} str mp lold h pointstolist
      = existsPointLC (just newfin) (str ∷ lold) (lemmaCons1 String (HeapObjectStrfin h)
                      (corHeapObjectLL String h) mp lold pointstolist str) (refl , refl)


headDirect : List String → Maybe String
headDirect [] = nothing
headDirect (x ∷ l) = just x


tailDirect : List String → List String
tailDirect [] = []
tailDirect (x ∷ l) = l


headHeapRelation : (w : World)
                   (lold : List String)
                   (w' : World)
                   (a : w' ≡ w  ×' Maybe String)
                   (h : LLStrfin  w')
                   (mp : MPointerfin w')
                   (lnew : List String)
                   (pointstolist : PointsToListStrLL h mp lnew)
                   (a' : Unit) → Set
headHeapRelation w lold w' a h mp lnew pointstolist q' = (headDirect lold) ≡ (pr₂ a) ×' (lnew ≡ lold)


bisimProofHead : {w : World} (mp : MPointerfin w) (lold : List String)
                 (h : LLStrfin  w)
                 (pointstolist : PointsToListStrLL h mp lold)
                 → SimFull+ ∞ (λ _ w' → w' ≡ w  ×' Maybe String) Unit
                           (headHeapRelation w lold)
                           w (headHeapProgIndCoind+ pointerStructfin {String} {w} mp)
                           h mp lold pointstolist emptySessionProg+
bisimProofHead {w} (just p) [] h ()
bisimProofHead {w} (just p) (.(↑ h p .getElemLL) ∷ lold) h (consp x) = existsPointLC (just p) ((↑ h p .getElemLL) ∷ lold) (consp x)  (refl , refl) --  --
bisimProofHead {w} nothing [] h pointstolist = refl , refl
bisimProofHead {w} nothing (x ∷ lold) h ()


tailHeapRelation : (w : World)
                   (lold : List String)
                   (w' : World)
                   (a : w' ≡ w  ×' MPointerfin w')
                   (h : LLStrfin  w')
                   (mp : MPointerfin w')
                   (lnew : List String)
                   (pointstolist : PointsToListStrLL h mp lnew)
                   (a' : Unit) → Set
tailHeapRelation w lold w' a h mp lnew pointstolist q' = lnew ≡ tailDirect lold

bisimProofTail : {w : World} (p : Pointerfin w) (lold : List String)
                 (h : LLStrfin  w)
                 (pointstolist : PointsToListStrLL h (just p) lold)
                 → SimFull+ ∞ (λ _ w' → w' ≡ w  ×' MPointerfin w') Unit
                           (tailHeapRelation w lold)
                           w (tailHeapProgIndCoind+ pointerStructfin {String} {w} p)
                           h (just p) lold pointstolist emptySessionProg+
bisimProofTail {w} p [] h ()
bisimProofTail {w} p (.(↑ h p .getElemLL) ∷ lold) h (consp x) = existsPointLC (↑ h p .getNextLL) lold x refl
