
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
  'ns s c' =. _1 1 2 o y
  ns (<x2,x1) } s (<x1,x2) } c ((x2,x2); x1, x1) } (=i.d)
)

NB. TODO: add in the missing edges.
NB. TODO: add some sliders to control the matrix (see "deoptim" demo)

NB. verb to calculate adjacency matrix for the hypercube vertices
NB. (vertices here are adjacent when they differ by 1 bit)
adj=: [: I. 1 = [: +/"1 ~:"1/~

NB. verb to find the unique edges.
NB. returns a k*2 array with two ints per row, representing node indices
edges =: (0 0 -.~ [: ,/ (i.@#) ([ ,"0 < # ])"0 1 adj)

NB. dot product
dot =: (+/ .*)

NB. rot3d = roll, pitch, yaw
rot3d =: [: dot/ (3 1 2, 3 0 2 ,: 3 0 1) (romat"1 0) 3 {. ]

lines =: [: ,/"2 [: -: ]

NB. draw a cube:
gdlines gddraw lines ortho2d (rot3d 30 25 50 deg) dot~  v 3


NB. ---- working version -------------------------------

edges =: <"2@{{  NB. edges of a y-dimensional hypercube
  o =. y#0                     NB. origin for k-dimensional space
  b =. =i.y                    NB. basis vectors in the space
  e =. (0,2,y)$0               NB. an (empty) list of pairs of points
  f =. ,:o                     NB. the frontier (list of unvisited points)
  for. i.y do.
    nf=. ,/f +."1/ b           NB. new frontier (after exploring along all axes)
    ne=. ((y*#f)$f),:"1 nf     NB. new edges (but we've already saturated some dimensions)
    ke=.({~ [:I. -.@-:/"2) ne  NB. keep the edges that reached new points
    f =. nf                    NB. update the frontier
    e =. ~.e,ke                NB. append the new edges
  end. }}

[ pt =: edges 0
[ ln =: edges 1
[ sq =: edges 2
[ cu =: edges 3
[ ts =: edges 4

np =: {{#~.,/>y}}
np each pt;ln;sq;cu;<ts

NB. this actually draws a cube!
gdlines gddraw lines ortho2d (rot3d 30 25 50 deg) dot~ > cu

NB. todo: now go back and draw the tesseract.
