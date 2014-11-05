
NB. drawing a tesseract in j (unfinished)
NB. -------------------------------------

require 'graph'

NB. let v N be the spatial coordintes of an n-dimensional unit hypercube.
v =: [: #: [: i.2^]
V =: v N=:4

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
draw0 =: verb def '(([[gdlines gddraw) ,@:-:@:ortho2d RMAT (+/ .*)"_ 1 cyc graycode y'
NB. usage: draw0 V

NB. Unfortunately, while the graycoding idea got me a continuous
NB. path that visits each vertex (a hamiltonian path), it doesn`t
NB. include all the edges, so the result looks funny.

NB. -------

NB. wrap circle function to treat negative signs differently:
o =: (*@:[ * |@:[ o. ])"1 0  NB. (-x) o y  <=>  -(x o. y)

NB. deg suffix to convert degrees to radians:
deg =: 1 : 'm * 1r180p1'

NB. matrix to rotate by y radians in x0 dimensions using the x1,x2 plane
romat =: dyad define
  assert. (d > x1,x2) *. (x1 ~: x2) [ 'd x1 x2' =. x
  'ns s c' =. _1 1 2 o. y
  ns (<x2,x1) } s (<x1,x2) } c ((x2,x2); x1, x1) } (=i.d)
)

NB. TODO: add in the missing edges.
NB. TODO: add some sliders to control the matrix (see "deoptim" demo)

NB. verb to calculate adjacency matrix for the hypercube vertices
NB. (vertices here are adjacent when they differ by 1 bit)
adj=: [: I. 1 = [: +/"1 [: = "1/~ ]

NB. same thing for opposite corner of a face.
NB. (vertices here are opposite when they differ by 2 bits)
opp=: [: I. 2 = [: +/"1 [: = "1/~ ]

