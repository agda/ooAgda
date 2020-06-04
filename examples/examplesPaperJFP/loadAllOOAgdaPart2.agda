module examplesPaperJFP.loadAllOOAgdaPart2 where


-- This is a continuation of the file loadAllOOAgdaPart1
-- giving the code from the ooAgda paper
-- This file was split into two because of a builtin IO which
-- makes loading files from part1 and part2 incompatible.

-- Note that some files which are directly in the libary can be found
-- in loadAllOOAgdaFilesAsInLibrary

-- Sect 1 - 7 are in loadAllOOAgdaPart1.agda

-- 8. State-Dependent Objects and IO
-- 8.1 State-Dependent Interfaces

import examplesPaperJFP.StatefulObject

-- 8.2 State-Dependent Objects
-- 8.2.1. Example of Use of Safe Stack

import examplesPaperJFP.safeFibStackMachineObjectOriented

-- 8.3 Reasoning About Stateful Objects

import examplesPaperJFP.StackBisim

-- 8.3.1. Bisimilarity
-- 8.3.2. Verifying stack laws}
-- 8.3.3. Bisimilarity of different stack implementations


-- 8.4. State-Dependent IO

import examplesPaperJFP.StateDependentIO

-- 9. A Drawing Program in Agda


-- code as in paper adapted to new Agda
open import examplesPaperJFP.IOGraphicsLib
-- code as in library see loadAllOOAgdaFilesAsInLibrary.agda
-- open import SizedIO.IOGraphicsLib
open import examplesPaperJFP.ExampleDrawingProgram

-- 10. A Graphical User Interface using an Object
-- 10.1. wxHaskell
-- 10.2. A Library for Object-Based GUIs in Agda

open import examplesPaperJFP.VariableList
open import examplesPaperJFP.WxGraphicsLib
open import examplesPaperJFP.VariableListForDispatchOnly

-- 10.3 Example: A GUI controlling a Space Ship in Agda

open import examplesPaperJFP.SpaceShipSimpleVar
open import examplesPaperJFP.SpaceShipCell
open import examplesPaperJFP.SpaceShipAdvanced

-- 11. Related Work

open import examplesPaperJFP.agdaCodeBrady

-- 12. Conclusion
-- Bibliography
