module ConsoleLib where

open import NativeIO public
open import SizedIO.Console public  hiding (main) renaming (translateIOConsole to run)
open import Size
open import SizedIO.Base
open import Data.List
open import Data.Bool
open import Data.String

infix 10 _==str_
_==str_ : String → String → Bool
s ==str s' = s == s'

WriteString : ∀{i} → (s : String) → IOConsole i Unit
WriteString s = Do (putStrLn s)

GetLine : ∀{i} → IOConsole i String
GetLine = Do getLine

-- In order for the recursion of a recursive IO program not to unfold,
--  on needs to eliminate the lead program using the observation for IO
--  which is force.
-- So the program needs to be written as
--   force (myprog args) = ...
-- The resulting program needs to be in IOConsole'.
-- the following funcitions WriteString+ and GetLine+
-- create programs in IOConsole', assuming a continuing program which
-- is in IOConsole
-- they contain one IO interaction which is required for the program to be
-- productive.



WriteString+ : ∀{i} → {A : Set}(s : String)(p : IOConsole i A)
               → IOConsole' i A
WriteString+ s p = do' (putStrLn s) λ _ → p

GetLine+ : ∀{i} → {A : Set}(p : String → IOConsole i A)
               → IOConsole' i A
GetLine+ f = do' getLine f


ConsoleProg : Set
ConsoleProg = NativeIO Unit
