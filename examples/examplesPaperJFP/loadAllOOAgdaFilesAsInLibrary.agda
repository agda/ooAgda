module examplesPaperJFP.loadAllOOAgdaFilesAsInLibrary where


-- this file loads those files from the ooAgda paper
-- which occur in the library as well
-- the code as it occurred in the original paper after adapting to current Agda
--    including any code not found directly inthe library
--    can be found in loadAllOOAgdaPart1.agda
--    and             loadAllOOAgdaPart2.agda

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

-- 8. State-Dependent Objects and IO
-- 8.1 State-Dependent Interfaces
-- 8.2 State-Dependent Objects
-- 8.2.1. Example of Use of Safe Stack
-- 8.3 Reasoning About Stateful Objects
-- 8.3.1. Bisimilarity
-- 8.3.2. Verifying stack laws}
-- 8.3.3. Bisimilarity of different stack implementations
-- 8.4. State-Dependent IO
-- 9. A Drawing Program in Agda

open import SizedIO.IOGraphicsLib


-- 10. A Graphical User Interface using an Object
-- 10.1. wxHaskell
-- 10.2. A Library for Object-Based GUIs in Agda

open import StateSizedIO.GUI.VariableList
open import StateSizedIO.GUI.WxGraphicsLib

-- 10.3 Example: A GUI controlling a Space Ship in Agda

open import StateSized.GUI.SpaceShipSimpleVar
open import StateSized.GUI.SpaceShipCell
open import StateSized.GUI.SpaceShipAdvanced

-- 11. Related Work
-- 12. Conclusion
-- Bibliography
