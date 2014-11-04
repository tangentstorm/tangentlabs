
NB. drawing a tesseract in j (unfinished)
NB. -------------------------------------

require 'graph'

NB. let V be the spatial coordintes of an n-dimensional unit hypercube.
V =: #: i.2^N=:4

NB. order the nodes so that we visit each vertex in turn
NB. (a "hamiltonian path" or "traceable path"). This is done
NB. by converting the binary numbers to their gray code representation.
graycode =: (0 ,~ ] ~: 0 , }:)"1

NB. Make the path into a cycle by appending a copy of the first node.
cyc =: ,{.

NB. Generate a random transformation matrix.
RMAT =: ?(,~N+1)$0

NB. perform othographic projection to 2d,
NB. by taking only the first 2 items of each point.
ortho2d =: 2&{. "1

NB. put it all together, scale by half, and render to screen.
(([[gdlines gddraw) ,@:-:@:ortho2d RMAT (+/ .*)"_ 1 cyc graycode V

NB. Unfortunately, while the graycoding idea got me a continuous
NB. path that visits each vertex (a hamiltonian path), it doesn't
NB. include all the edges, so the result looks funny.

NB. TODO: add in the missing edges.
NB. TODO: add some sliders to control the matrix (see "deoptim" demo)
