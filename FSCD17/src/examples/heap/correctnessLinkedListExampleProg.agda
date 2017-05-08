--@PREFIX@correctnessLinkedListExampleProg
{-# OPTIONS --postfix-projections #-}


module examples.heap.correctnessLinkedListExampleProg where

open import Relation.Binary.PropositionalEquality hiding (sym)
open import Data.String renaming (_==_ to _==Str_)
open import Data.Maybe hiding (maybe)
open import Size hiding (↑_)

open import src.NativeIO

open import src.heap.heapAsObjectBase hiding (Pointer)
open import src.heap.heapAsObjectGeneric

open import src.StateSizedIO.writingOOsUsingIOReaderMethods hiding (nˢ)

open import src.SizedIO.Console using (consoleI; translateIOConsoleLocal; putStrLn; getLine)

open import Data.Bool.Base

open import Data.Product renaming (proj₁ to pr₁; proj₂ to pr₂; _×_ to _×'_; map to mapp)

open import src.heap.heapAsObject hiding (readP;writeP)

open import examples.heap.correctnessLinkedList
open import examples.heap.correctnessLinkedListStep2



data StackCmd : Set where
  push pop top undefcmd : StackCmd

str2StackCmd : String → StackCmd
str2StackCmd s = if (s ==Str "push") then push
         else (if (s ==Str "pop") then pop
         else (if (s ==Str "top") then top
         else undefcmd))

maybeStringToString : Maybe String → String
maybeStringToString (just s) = s
maybeStringToString nothing = "got nothing"


module _ (pointStruct : PointerStruct)
         (let Pointer = Pointer pointStruct)
         (let embedp = embedp pointStruct) where

  -- Type of program: IO, returning Unit, interacting with console and heap.

  IOU  = λ i w → IOˢindcoind  ConsoleInterfaceˢ (HeapInterfaceˢIO Pointer (gLinkedWP String pointStruct)) i (λ _ w' → Unit) unit w
--@BEGIN@IOUplus
  IOU+ = λ i w → IOˢindcoind+ ConsoleInterfaceˢ (HeapInterfaceˢIO Pointer (gLinkedWP String pointStruct)) i (λ _ w' → Unit) unit w
--@END
  -- readCmd : {i : Size}{w : World} → IOU+ i w
  -- readCmd = doˢIO getLine λ str → {!returnˢic!}

  mutual

    -- Entry point.

    exampleProg : {i : Size}{w : World}(mp : Maybe (Pointer w)) → IOU i w
    exampleProg mp .forceIC {j} = exampleProg+ {j} mp

    -- Read a command from the console.
--\correctnessLinkedListExampleProg
--@BEGIN@exampleProg
    exampleProg+ : {i : Size} {w : World} (mp : Maybe (Pointer w)) → IOU+ i w
    exampleProg+ mp =  doˢIO getLine λ str →  exampleProgStep2 mp (str2StackCmd str)
--@HIDE-BEG

    exampleProgStep2 : {i : Size} {w : World} (mp : Maybe (Pointer w)) (cmd : StackCmd) → IOU i w
--@HIDE-END
    exampleProgStep2 mp cmd .forceIC {j} = exampleProgStep2+ mp cmd
--@HIDE-BEG
    -- Interpret command.

    exampleProgStep2+ : {i : Size} {w : World} (mp : Maybe (Pointer w)) (cmd : StackCmd) → IOU+ i w

    -- Push: read an element from the console and put it onto the stack.
--@HIDE-END
    exampleProgStep2+ mp push =
      doˢIO getLine λ str →  consHeapProgIndCoind pointStruct String str mp  >>=indcoind  λ{ (ww' , p) →
      exampleProg+ (just p) }
--@END
    -- Top: print the top element.

    exampleProgStep2+ mp top =
      headHeapProgIndCoind+ pointStruct mp  >>=indcoind+  λ{ (refl , ms) →
       doˢIO (putStrLn (maybeStringToString  ms)) λ _ →
       exampleProg mp}


    exampleProgStep2+ (just p) pop =
      tailHeapProgIndCoind+ pointStruct p  >>=indcoind+  λ{ (ww' , p') →
       exampleProg+ p'                                    }

    -- Pop (empty stack): print error message.

    exampleProgStep2+ nothing pop =
      doˢIO (putStrLn "Error -  Stack is empty") λ _ →
      exampleProg nothing

    -- Invalid command: print error message.

    exampleProgStep2+ mp undefcmd =
      doˢIO (putStrLn "Please enter top, pop, or push") λ _ →
      exampleProg mp



mainHeapProgram : NativeIO Unit
mainHeapProgram = run+ exampleProg+ pointerStructfin {∞} {∅w} nothing  startingWith startHeap


main = mainHeapProgram
