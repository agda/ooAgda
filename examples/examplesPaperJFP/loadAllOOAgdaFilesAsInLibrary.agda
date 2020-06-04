module examplesPaperJFP.loadAllOOAgdaFilesAsInLibrary where


-- this file loads those files from the ooAgda paper
-- which occur in the library as well
-- the code as it occurred in the original paper after adapting to current Agda
--    including any code not found directly inthe library
--    can be found in loadAllOOAgda.agda

-- Source of paper:
--  Andreas Abel, Stephan Adelsberger, Anton Setzer:
--    Interactive Programming in Agda - Objects and Graphical User Interfaces
--    Journal of Functional Programming, 27, 2017
--    doi: http://dx.doi.org/10.1145/2976022.2976032
--    authors copy: http://www.cs.swan.ac.uk/~csetzer/articles/TyDe2016.pdf
--    bibtex: http://www.cs.swan.ac.uk/~csetzer/articles/TyDe2016.bib
--    Presentation video
--    https://www.youtube.com/watch?v=0pnqynBqGOQ&list=PLnqUlCo055hUFzMkHyGOvOc0jNbv_bd26&index=7
--    Presentation slides
--    http://www.cs.swan.ac.uk/~csetzer/slides/TyDe/2016/slidesTyDe2016BasharIgried.pdf


-- 1. Introdution
-- 2. Introduction to Agda
-- 3. Coalgebras in Agda
-- 3.1. Coalgebra by example: Colists
-- 3.2. Coalgebras in General
-- 4. Interactive Programs in Agda
-- 4.1. Interaction interfaces
-- 4.2. Interaction trees
-- 4.3. Running interactive programs
-- 5. Objects in Agda

-- code as in paper adapted to new Agda
-- open import examplesPaperJFP.Object
-- code as in library
open import SizedIO.Object

-- 6. Sized Coinductive Types
-- 7. Interface Extension and Delegation

-- code as in paper adapted to new Agda
-- open import examplesPaperJFP.CounterCell
-- code as in library
open import Sized.CounterCell



{-
open import CatNonTerm
open import CatTerm
open import Coalgebra
open import Colists
open import Collatz
open import ConsoleInterface
open import Console
open import CounterCell
-- open import ExampleDrawingProgram
open import IOExampleConsole
-- open import IOGraphicsLib
-- open import  loadAllForChecking.agda
-- open import  loadAllForCheckingPart2.agda
open import NativeIOSafe
open import Object
open import Sized
-- open import SpaceShipAdvanced
-- open import SpaceShipCell
-- open import SpaceShipSimpleVar
-- open import StackBisim
-- open import StateDependentIO
-- open import StatefulObject
-- open import StatefulStackProgram
-- open import VariableListForDispatchOnly
-- open import VariableList
-- open import WxBindingsFFI
-- open import WxGraphicsLib
-}