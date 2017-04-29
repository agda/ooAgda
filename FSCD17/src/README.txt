Loading everything plus guide to code
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The file 
   src/examples/heap/ALL.agda

loads everything.

It contains as well as comments a guide to where files are located.


Installation
~~~~~~~~~~~~~~
To install add  full path to the file
  src/ooAgda-FSCD17.agda-lib

to the agda libraries file (under Linux located in ~/.agda/libraries)

You need to have as well the standard library installed
with a file std-lib.agda-lib in the src directory
containing the following (excluding the lines starting with --)

-- begin code --
name: std-lib
include: .
-- end code --

Add as well the path to this library file to the agda libraries file.
  
We type checked the library with the version of agda on github
   https://github.com/agda/agda
   Vers 4958ed9  on Thu Mar 30 19:44:38 2017 +0200

   https://github.com/agda/agda-stdlib
   Vers c36ab69  on Fri Mar 17 18:55:08 2017 +0000

HTML version
~~~~~~~~~~~~
An HTML version can be found at

https://stephanadl.github.io/ooAgdaHtml/examples.heap.ALL.html


