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
with a file std-lib.agda-lib containing the following (excluding the 
lines starting with --)

-- begin code --
name: std-lib
include: .
-- end code --

Add as well the path to this file added as well to the agda libraries file.
  


HTML version
~~~~~~~~~~~~
An HTML version can be found at

https://stephanadl.github.io/ooAgdaHtml/examples.heap.ALL.html


