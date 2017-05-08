
{-# OPTIONS --postfix-projections #-}



module examples.benchmarks.binaryTreeBenchmark where

-- standard lib
--
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function using (case_of_)

open import Data.Bool.Base using (T; if_then_else_; true; false)
open import Data.String using (_++_; String)
open import Data.Maybe using (just; nothing; Maybe)
open import Data.List.Base hiding (_++_)

open import Data.Nat.Base hiding (_≟_) renaming (_⊔_ to _⊔n_;  _*_ to _*Nat_; _+_ to _+Nat_)

open import Size using (Size; ∞)

open import Data.Integer.Base hiding (suc)
open import Data.Integer using (show)


-- lib
--
open import src.NativeIO using (unit; Unit; primShowNat; getArgs; NativeIO; _native>>=_; nativePutStrLn)
open import src.SizedIO.Console using (putStrLn; getLine; consoleI; translateIOConsoleLocal)
open import src.StateSizedIO.writingOOsUsingIOReaderMethods using (IOˢindcoind+; ConsoleInterfaceˢ; returnˢic; doˢobj; _>>=indcoind+_; doˢIO; delayˢic; _>>=indcoind_; IOˢindcoind; forceIC)

-- heap imports
--
open import src.heap.libraryNat using (refl≦ℕb; trans≦ℕb; n≦ℕbsucn)

open import src.heap.library using (_×_; _,,_)
open import src.heap.libraryMaybe using (NativeMaybe; nativeMaybeFunc; justNative; nothingNative)

open import src.heap.heapAsObjectBase using (World; _≦w_; sucw)
open import src.heap.heapAsObjectGeneric using (Pointer; embedp)

open import src.heap.heapAsObjectNativeHeap using (IORef)

open import src.heap.heapAsObject using (readP; newP)


open import examples.benchmarks.libraryFastInt using (toInt; _^Int_; fromInt; showInt; _*Int_)


open import examples.benchmarks.nativeBinaryTree

open import examples.benchmarks.genericNativeHeap


record Node' (A : Set) (Point : Set) :  Set where
  constructor node'
  field
    item'  : A
    left'  : NativeMaybe Point
    right' : NativeMaybe Point

open Node' public


nativeNodeConstr' : {A : Set} (n : Node' A (IORef (nativeLL A))) → nativeLL A
nativeNodeConstr' {A} (node' item left right) = nativeNodeConstr item left right
{-# INLINE nativeNodeConstr' #-}

nativeNodeUnfold' : {A : Set} (x : nativeLL A) → Node' A (IORef (nativeLL A))
nativeNodeUnfold' x = node' (getItem x) (getLeft x) (getRight x)
{-# INLINE nativeNodeUnfold' #-}


open genericNativeImpl (nativeLL ℤ) (Node'  ℤ) (nativeNodeConstr' {ℤ}) nativeNodeUnfold'


module _  where

  -- module may be generalized over this definition
  --
  embedBH+ : {w w' : World} → T (w ≦w w') → iorefPointerStructGen .Pointer w → iorefPointerStructGen .Pointer w'
  embedBH+ {w} {w'} = λ _ x → x
  {-# INLINE  embedBH+ #-}



  bottomUpTree : (i : Size)(w : World)(item : ℤ)(depth : ℕ)
                  → IOˢindcoind+ ConsoleInterfaceˢ heapInter
                         i (λ _ w' → iorefPointerStructGen .Pointer w' × T (w ≦w w')) unit w
  bottomUpTree i w item zero = doˢobj (newP (node' item nothingNative nothingNative)) λ p →
                               returnˢic (p ,, n≦ℕbsucn{w})

  bottomUpTree i w item (suc depth) = bottomUpTree i w (item + item - + 1) depth
                                                      >>=indcoind+ λ { {_}{w'} (pLeft ,, w≦ww')  →

                                      bottomUpTree i w' (item + item) depth
                                                      >>=indcoind+ λ { {_}{w''} (pRight ,, w'≦ww'') →

                                      doˢobj (newP (node' item
                                                         (justNative (iorefPointerStructGen .embedp{w'} (embedBH+ {w'}{w''} w'≦ww'' pLeft)))
                                                         (justNative (iorefPointerStructGen .embedp{w'} pRight)))) λ pReturn →

                                      returnˢic (pReturn ,, trans≦ℕb w w' (sucw w'') w≦ww'
                                                               (trans≦ℕb w' w'' (sucw w'') w'≦ww''
                                                               (n≦ℕbsucn{w''})))
                                      }}


  checkTree  : (i : Size) → (w : World) → (iorefPointerStructGen .Pointer w) → (depth : ℕ)
                  → IOˢindcoind+ ConsoleInterfaceˢ heapInter
                         i (λ _ w' → ℤ × T (w ≦w w')) unit w
  checkTree i w p zero = returnˢic ((+ 0) ,, refl≦ℕb w)
  checkTree i w p (suc depth) =  doˢobj (readP p) λ {
                                   (node' item nothingNative _) → returnˢic ((+ 1) ,, refl≦ℕb w)
                                 ; (node' item _ nothingNative) → returnˢic ((+ 1) ,, refl≦ℕb w)
                                 ; (node' item (justNative left) (justNative right)) →

                                 checkTree i w left depth >>=indcoind+ λ { {_}{w'} (leftRes ,, w≦ww') →
                                 checkTree i w' (embedBH+{w}{w'} w≦ww' right) depth >>=indcoind+ λ { {_}{w''} (rightRes ,,  w'≦ww'') →
                                 returnˢic ((+ 1 + leftRes + rightRes) ,,  trans≦ℕb w w' w'' w≦ww' w'≦ww'')
                                 }}}

  checkBottomUpTree : (i : Size)(w : World)(item : ℤ)(depth : ℕ)
                  → IOˢindcoind+  ConsoleInterfaceˢ heapInter i (λ _ w' → ℤ × T (w ≦w w')) unit w


  checkBottomUpTree i w item depth =  bottomUpTree i w item depth >>=indcoind+ λ { {_}{w'} (pointerTree ,, w≦ww') →
                                      checkTree i w' pointerTree (sucw depth) >>=indcoind+ λ { {_}{w''} (checkNum ,, w'≦ww'') →
                                      returnˢic (checkNum ,,  trans≦ℕb w w' w'' w≦ww' w'≦ww'')
                                      }}


  forInner : (i : Size)(w : World)(j :  ℕ)(checkVal : ℤ) (depth : ℕ)
                  → IOˢindcoind+
                         ConsoleInterfaceˢ
                          heapInter
                         i (λ _ w' → ℤ × T (w ≦w w')) unit w
  forInner i w zero check _ = returnˢic (check ,, refl≦ℕb w)
  forInner i w (suc j) check depth = checkBottomUpTree i w (+ suc j) depth >>=indcoind+  λ { {s}{w'} (check1 ,, w≦ww')  →
                                     checkBottomUpTree i w' (+ 0 - + suc j) depth >>=indcoind+ λ { {s'}{w''} (check2 ,, w'≦ww'')  →
                                     forInner i w'' j (check + check1) depth  >>=indcoind+ λ { {s'}{w'''} (checkRes ,, w''≦ww''') →
                                     returnˢic (checkRes ,, trans≦ℕb w w'' w''' (trans≦ℕb w w' w'' w≦ww' w'≦ww'') w''≦ww''' )}}}



  forOuter : (i : Size)(w : World)(depth : ℕ) → (maxDepth : ℕ) → (minDepth : ℕ)
                  → IOˢindcoind+ ConsoleInterfaceˢ heapInter
                         i (λ _ w' →  T (w ≦w w')) unit w
  forOuter i w (suc (suc d)) maxDepth minDepth with ⌊ minDepth ≤? (suc (suc d)) ⌋
  ... | true =
    let depth = suc (suc d)
        realDepth = + maxDepth - + depth + + minDepth
        iterations = (toInt 2) ^Int (toInt ∣ (+ maxDepth - realDepth + + minDepth) ∣)

    in forInner i w (fromInt iterations) (+ 0) ∣ realDepth ∣  >>=indcoind+ λ { {_} {w'} (resInner ,, w≦ww') →
        doˢIO (putStrLn (showInt (iterations)
                         ++ "\t trees of depth " ++ show realDepth ++ "\t check: " ++ show resInner)) λ _ →
                         delayˢic (forOuter i w' d maxDepth minDepth) >>=indcoind λ { {_} {w''} (w'≦ww'') →
                         returnˢic (trans≦ℕb w w' w'' w≦ww' w'≦ww'')
                         }}


  ... | false = returnˢic (refl≦ℕb w)
  forOuter i w _ _ _ =  returnˢic (refl≦ℕb w)


  mainProg : (n : ℕ)
             → IOˢindcoind+ ConsoleInterfaceˢ heapInter
                         ∞ (λ _ w' → Unit) unit zero
  mainProg n     = let
                     minDepth : ℕ
                     minDepth = 4
                     maxDepth : ℕ
                     maxDepth = if ⌊ n ≤? (minDepth +Nat 2) ⌋
                                  then minDepth +Nat 2 else n
                     stretchDepth : ℕ
                     stretchDepth = suc maxDepth

                   in checkBottomUpTree ∞ zero (+ 0) stretchDepth >>=indcoind+  λ { {_} {w'} (checkValStretched ,, w≦ww') →
                      doˢIO (putStrLn ("stretch tree of depth "
                        ++ primShowNat stretchDepth ++ "\t check: " ++ show checkValStretched)) λ _ →

                      delayˢic (bottomUpTree ∞ w' (+ 0) maxDepth) >>=indcoind λ { {_} {w''} (ptrLongLivedTree ,,  w'≦ww'') →

                      -- For:
                      forOuter ∞ w'' maxDepth maxDepth minDepth >>=indcoind+ λ { {_} {w'''} (w''≦ww''') →

                      checkTree ∞ w''' (embedBH+{w''}{w'''} w''≦ww''' ptrLongLivedTree)
                                       (sucw maxDepth) >>=indcoind+ λ { {_} {w''} (checkLong ,, w'''≦ww'''') →
                      doˢIO (putStrLn ("long lived tree of depth " ++ show (+ maxDepth) ++ "\t check: " ++ show checkLong)) λ _ →
                      delayˢic (returnˢic _)
                   }}}}



prgGen : ℕ → IOˢindcoind+ ConsoleInterfaceˢ heapInter ∞ (λ _ _ → Unit) unit zero
prgGen n = mainProg n
{-# INLINE  prgGen #-}

prgGen' : ℕ → IOˢindcoind ConsoleInterfaceˢ heapInter ∞ (λ _ _ → Unit) unit zero
prgGen' n .forceIC = prgGen n
{-# INLINE  prgGen' #-}

mainBinaryTranslatedViaNativeHeap' : ℕ → NativeIO Unit
mainBinaryTranslatedViaNativeHeap' n = translate2NativeGen (prgGen' n)
{-# INLINE  mainBinaryTranslatedViaNativeHeap' #-}


postulate
  readMaybeℕ : String → Maybe ℕ

{-# FOREIGN GHC import qualified Text.Read #-}
{-# COMPILE GHC readMaybeℕ = (\s -> Text.Read.readMaybe (Data.Text.unpack s)) #-}


parseOneArg : List String → Maybe  ℕ
parseOneArg (s₁ ∷ []) with readMaybeℕ s₁
... | just num₁ = just num₁
... | _ = nothing
parseOneArg _ = nothing


mainBinaryTranslatedViaNativeHeap : NativeIO Unit
mainBinaryTranslatedViaNativeHeap =
         getArgs native>>= λ args →
         case (parseOneArg args) of λ {
         (just n) → mainBinaryTranslatedViaNativeHeap' n;

         _ → nativePutStrLn "need excactly one argument: the maxDepth of the tree"
         }
{-# INLINE  mainBinaryTranslatedViaNativeHeap #-}


main = mainBinaryTranslatedViaNativeHeap
{-# INLINE main #-}
