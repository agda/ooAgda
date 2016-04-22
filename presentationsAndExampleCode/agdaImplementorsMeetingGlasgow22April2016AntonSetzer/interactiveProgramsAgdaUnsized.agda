module interactiveProgramsAgdaUnsized where

open import NativeIO
open import Function


record IOInterface : Set₁ where
  field  Command   :  Set
         Response  :  (c : Command) → Set

open IOInterface public

mutual
  record IO (I : IOInterface)  (A : Set) : Set where
     coinductive
     constructor delay
     field force : IO' I A

  data IO' (I : IOInterface)  (A : Set) : Set where
    do'     : (c : Command I) (f : Response I c → IO I A)  → IO' I A
    return' : (a : A)                                       → IO' I A

open IO public

module _ {I : IOInterface} (let C = Command I) (let R = Response I) where
  do  : ∀{A} (c : C) (f : R c → IO I A) → IO I A
  force (do c f) = do' c f

  return : ∀{A} (a : A) → IO I A
  force (return a) = return' a

  infixl 2 _>>=_

  _>>=_ :  ∀{A B} (m : IO I A) (k : A → IO I B) → IO I B
  force (m >>= k) with force m
  ... | do' c f   = do' c λ x → f x >>= k
  ... | return' a = force (k a)


  {-# NON_TERMINATING #-}
  translateIO : ∀ {A} (tr : (c : C) → NativeIO (R c)) → IO I A → NativeIO A
  translateIO tr m = case (force m) of λ
     {  (do' c f)    →  (tr c) native>>= λ r → translateIO tr (f r)
     ;  (return' a)  →  nativeReturn a
     }


data ConsoleCommand : Set where
  getLine   :  ConsoleCommand
  putStrLn  :  String → ConsoleCommand

ConsoleResponse : ConsoleCommand → Set
ConsoleResponse  getLine      =  String
ConsoleResponse (putStrLn s)  =  Unit

ConsoleInterface : IOInterface
Command ConsoleInterface  = ConsoleCommand
Response ConsoleInterface = ConsoleResponse


IOConsole : Set → Set
IOConsole = IO ConsoleInterface

translateIOConsoleLocal : (c : ConsoleCommand) → NativeIO (ConsoleResponse c)
translateIOConsoleLocal (putStrLn s)  =  nativePutStrLn s
translateIOConsoleLocal getLine       =  nativeGetLine

translateIOConsole : {A : Set} → IOConsole A → NativeIO A
translateIOConsole = translateIO translateIOConsoleLocal


{-# NON_TERMINATING #-}
cat   :  IOConsole Unit
force cat =  do' getLine λ{ line → 
             do (putStrLn line)   λ _ →
             cat
             }

mutual
  cat' :  IOConsole Unit
  force cat' =  do' getLine λ{ line → 
                cat'' line}

  cat'' : String → IOConsole Unit
  force (cat'' line) = do' (putStrLn line)   λ _ →
                       cat'                                


main : NativeIO Unit
main = translateIOConsole cat
