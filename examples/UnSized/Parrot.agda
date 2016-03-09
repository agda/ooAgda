module UnSized.Parrot where

open import Data.Product
open import Data.String.Base

open import UnSizedIO.IOObject

open import UnSizedIO.Base hiding (main)
open import UnSizedIO.Console hiding (main)

open import NativeIO

open import UnSized.SimpleCell hiding (program; main)


--ParrotC : Set
--ParrotC = ConsoleObject (cellI String)

-- but reusing cellC from SimpleCell, as interface is ident!

-- class Parrot implements Cell {
--   Cell cell;
--   Parrot (Cell c) { cell = c; }
--   public String get() {
--     return "(" + cell.get() + ") is what parrot got";
--   }
--   public void put (String s) {
--     cell.put("parrot puts (" + s + ")");
--   }
-- }

-- parrotP is constructor for the consoleObject for interface (cellI String)
{-# NON_TERMINATING #-}
parrotP : (c : CellC) → CellC
(method (parrotP c) get) =
  do1 (putStrLn "printing works")  >>
  method c get >>= λ { (s , c') →
  return ("(" ++ s ++ ") is what parrot got" , parrotP c')  }
(method (parrotP c) (put s)) =
  method c (put ("parrot puts (" ++ s ++ ")"))
  


--   public static void main (String[] args) {
--     Parrot c = new Parrot(new SimpleCell("Start"));
--     System.out.println(c.get());
--     c.put(args[1]);
--     System.out.println(c.get());
--   }
-- }


program : String → IOConsole Unit
program arg =
  let c₀ = parrotP (cellP "Start") in
  method c₀ get       >>= λ{ (s , c₁) →
  do1 (putStrLn s)         >>
  method c₁ (put arg) >>= λ{ (_ , c₂) →
  method c₂ get       >>= λ{ (s' , c₃) →
  do1 (putStrLn s')        }}}

main : NativeIO Unit
main = translateIOConsole (program "hello")
