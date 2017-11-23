module consoleExamples.simpleLoop where

open import ConsoleLib
open import Data.Bool renaming (not to ¬)
open import Data.String renaming (_==_ to _==str_)
open import SizedIO.Base
open import Size

-- the following program asks the user for an input, which is a string.
-- It converts this string into a Boolean value (by mapping "true" to true and
--    "false" to false), applies Boolean negation to the result
-- and then converts the resulting Boolean value back to a string

boolStrInput2Bool : String → Bool
boolStrInput2Bool s = s ==str "true"

checkStrBoolInput : String → Bool
checkStrBoolInput s = (s ==str "true") ∨ (s ==str "false")


bool2Str : Bool → String
bool2Str true = "true"
bool2Str false = "false"


-- when writing a recursive program you need to write first the body
-- as an element of IOConsole
-- and apply an eliminator to it, followed by a a function which
--  results in an element of IOConsole'
-- otherwise the recursion would unfold and you get an infinite term
--
-- The functions WriteString+ and ReadLine+  which need the continuing program
--   as argument can be used to create elements of IOConsole'
--
-- Furthermore after applying a size argument (i which is of type Size)
--  the termination checker can figure out that your definition is productive
--  i.e. has at least one interaction before carrying out the recursion.

mainBody : ∀{i} → IOConsole i  Unit
force (mainBody) = WriteString+ "Enter true or false"
                   (GetLine >>= λ s →
                    if (checkStrBoolInput s) then
                       (WriteString ("Result of negating your input is " ++
                                    bool2Str (¬ (boolStrInput2Bool s))) >>= λ _ →
                        mainBody)
                     else
                       (WriteString ("Please enter \"true\" or \"false\"") >>= λ _ →
                       mainBody))

main : ConsoleProg
main = run mainBody
