module examplesPaperJFP.loadAllOOAgdaPart1 where


-- This file loads the files containing the code examples in the ooAgda paper
-- ordered by sections
-- The code is divided into files
--    loadAllOOAgdaPart1.agda and loadAllOOAgdaPart2.agda
-- loadAllOOAgdaPart1.agda loads code from Sect. 1 - 7
-- loadAllOOAgdaPart2.agda loads code from Sect. 8 - 12
--
-- The reason for splitting it into  two files is that because of some
--  Builtin the code from the first file cannot be loaded at the same
--  time as the code from the second one.
-- The difference is loading  NativeIOSafe.agda vs NativeIO.agda
--
-- Important changes due to updating it to current agda
-- ####################################################
--      * do is now a keyword and therefore replaced by exec
--      * some other small changes mainly because of changes in the
--           standard library have been made
--
-- Files from the Library
-- #########################
-- loadAllOOAgdaFilesAsInLibrary.agda
-- loads corresponding code from the library which is slightly different
--   from how it is represented in the paper


-- Source of paper, presentations, slides
-- #######################################
--  Andreas Abel, Stephan Adelsberger, Anton Setzer:
--    Interactive Programming in Agda - Objects and Graphical User Interfaces
--    Journal of Functional Programming, 27, 2017
--    doi: http://dx.doi.org/10.1145/2976022.2976032
--    authors copy: http://www.cs.swan.ac.uk/~csetzer/articles/ooAgda.pdf
--    bibtex: http://www.cs.swan.ac.uk/~csetzer/articles/ooAgda.bib


-- 1. Introdution
-- 2. Introduction to Agda

import examplesPaperJFP.finn
import examplesPaperJFP.exampleFinFun
import examplesPaperJFP.Equality

-- 3. Coalgebras in Agda
-- 3.1. Coalgebra by example: Colists

import examplesPaperJFP.Colists
import examplesPaperJFP.Collatz

-- 3.2. Coalgebras in General

import examplesPaperJFP.Coalgebra

-- 4. Interactive Programs in Agda
-- 4.1. Interaction interfaces

import examplesPaperJFP.NativeIOSafe
import examplesPaperJFP.BasicIO
import examplesPaperJFP.triangleRightOperator
import examplesPaperJFP.ConsoleInterface

-- 4.2. Interaction trees

import examplesPaperJFP.Console
import examplesPaperJFP.CatNonTerm
import examplesPaperJFP.CatTerm

-- 4.3. Running interactive programs

import examplesPaperJFP.IOExampleConsole

-- 5. Objects in Agda

-- code as in paper adapted to new Agda
import examplesPaperJFP.Object
-- code as in library see loadAllOOAgdaFilesAsInLibrary.agda
-- open import SizedIO.Object

-- 6. Sized Coinductive Types

import examplesPaperJFP.Sized

-- 7. Interface Extension and Delegation

-- code as in paper adapted to new Agda
import examplesPaperJFP.CounterCell
-- code as in library see loadAllOOAgdaFilesAsInLibrary.agda
-- open import Sized.CounterCell

--  *** Code from Sect 8 - 12 can be found in loadAllOOAgdaPart2.agda ***
