module interactiveProgramsAgda where

open import NativeIO
open import Function
open import Size
open import Data.Maybe.Base

record IOInterface : Set₁ where
  field  Command  : Set
         Response : (c : Command) → Set

open IOInterface public

mutual
  record IO (I : IOInterface) (i : Size) (A : Set) : Set where
     coinductive
     constructor delay
     field force : {j : Size< i} → IO' I j A

  data IO' (I : IOInterface) (i : Size) (A : Set) : Set where
    do'     : (c : Command I) (f : Response I c → IO I i A) → IO' I i A
    return' : (a : A)                                        → IO' I i A

open IO public


module _ {I : IOInterface} (let C = Command I) (let R = Response I) where
  do  : ∀{i A} (c : C) (f : R c → IO I i A) → IO I i A
  force (do c f) = do' c f

  return : ∀{i A} (a : A) → IO I i A
  force (return a) = return' a

  infixl 2 _>>=_

  _>>=_ :  ∀{i A B} (m : IO I i A) (k : A → IO I i B) → IO I i B
  force (m >>= k) with force m
  ... | do' c f   = do' c λ x → f x >>= k
  ... | return' a = force (k a)


  {-# NON_TERMINATING #-}
  translateIO : ∀ {A} (tr : (c : C) → NativeIO (R c)) → IO I ∞ A → NativeIO A
  translateIO tr m = case (force m) of λ
     {  (do' c f)    →  (tr c) native>>= λ r → translateIO tr (f r)
     ;  (return' a)  →  nativeReturn a
     }


{- Specific case of Console IO -}

data ConsoleCommand : Set where
  getLine   :  ConsoleCommand
  putStrLn  :  String → ConsoleCommand

ConsoleResponse : ConsoleCommand → Set
ConsoleResponse  getLine      =  String
ConsoleResponse (putStrLn s)  =  Unit

ConsoleInterface : IOInterface
Command ConsoleInterface  = ConsoleCommand
Response ConsoleInterface = ConsoleResponse

IOConsole : (i : Size) → Set → Set
IOConsole i = IO ConsoleInterface i

translateIOConsoleLocal : (c : ConsoleCommand) → NativeIO (ConsoleResponse c)
translateIOConsoleLocal (putStrLn s)  =  nativePutStrLn s
translateIOConsoleLocal getLine       =  nativeGetLine

translateIOConsole : {A : Set} → IOConsole ∞ A → NativeIO A
translateIOConsole = translateIO translateIOConsoleLocal

cat   :  ∀ {i} → IOConsole i Unit
force cat =  do' getLine λ line → 
             do (putStrLn line)   λ _ →
             cat


main : NativeIO Unit
main = translateIOConsole cat

