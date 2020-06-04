module Sized.Parrot where

open import Data.Product
open import Data.String.Base

open import SizedIO.IOObject

open import SizedIO.Base
open import SizedIO.Console hiding (main)
open import SizedIO.ConsoleObject

open import NativeIO

open import Sized.SimpleCell hiding (program; main)

open import Size

record Wrap A : Set where
  constructor wrap
  field unwrap : A

parrotI = cellJ (Wrap String)

ParrotC : (i : Size) → Set
ParrotC i = ConsoleObject i parrotI

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

parrotP : ∀{i} (c : CellC i) → ParrotC i
(method (parrotP c) get) =
  method c get >>= λ { (s , c') →
  return (wrap ("(" ++ s ++ ") is what parrot got") ,  parrotP c' )  }
(method (parrotP c) (put (wrap s))) =
  method c (put ("parrot puts (" ++ s ++ ")")) >>= λ { (_ , c') →
  return (_ ,  parrotP c') }



--   public static void main (String[] args) {
--     Parrot c = new Parrot(new SimpleCell("Start"));
--     System.out.println(c.get());
--     c.put(args[1]);
--     System.out.println(c.get());
--   }
-- }

program : String → IOConsole ∞ Unit
program arg =
  let c₀ = parrotP (cellP "Start") in
  method c₀ get               >>= λ{ (wrap s   , c₁) →
  exec1 (putStrLn s)            >>
  method c₁ (put (wrap arg))  >>= λ{ (_        , c₂) →
  method c₂ get               >>= λ{ (wrap s'  , c₃) →
  exec1 (putStrLn s')           }}}

main : NativeIO Unit
main = translateIOConsole (program "hello")

-- -}
