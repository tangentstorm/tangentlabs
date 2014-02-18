coclass 'Fountain'
NB. Fountains for J.
NB. ------------------------------------------------------------
NB. Fountains are a type of cyclic graph. They resembles trees
NB. but contain no null pointers, and can be navigated easily
NB. in any direction. In particular, (almost) all links are
NB. bi-directional, and there is a link connecting the top of
NB. the structure to the bottom.

NB. In this implementation, fountains are structured as tables
NB. with four columns, representing the four directions in which
NB. we can traverse the structure. The names of the directions
NB. are "up, down, previous, and next".
'up dn pv nx' =: i.4

NB. A fountain contains a minimum of two nodes. Node 0 is 
NB. called the 'hub', and is similar to the root of a tree.
NB. Node 1 is called the 'rim', and it models a doubly linked
NB. list connecting all the leaves of the tree.
'hub rim' =: i.2


NB. constructor
create =: monad define
  nav =: 1 1 0 0 ,: 0 0 1 1
  0 return.
)

NB. destructor
destroy =: ''codestroy&[]


NB. from :: nids <- directions <- nids
NB. (nid means 'node id'. e.g, 0 for the hub)
from =: dyad : 'x { y { nav'

NB. walk :: nids(s) <- start:nid(s) <- path=(dir,dir,dir...)
NB. monadic case walks starts from the hub
walk =: verb define "0 1
  0 $: y
:
  for_step. ;y do. x =. step from x end.
)

NB. -- formatting as s-expressions --
NB. ufsx : unformatted (i.e, non-pretty printed) s-expressions:
ufsx =: '()'"_



NB. examples / test cases
NB. ----------------------------------------------------------
a =. *./ & assert"0


NB. We can create a fountain simply by invoking the constructor:
ftn =. '' conew 'Fountain'

NB. Here is how a new fountain should look:
NB. u d p n
a   1 1 0 0 -: 0 { nav__ftn  NB. Node 0 is the hub, a ring up/dn from the rim.
a   0 0 1 1 -: 1 { nav__ftn  NB. Node 1 is the rim, a ring up/dn from the hub.
a   2 = # nav__ftn           NB. there are no other nodes

a  rim = (up,dn) from__ftn hub
a  hub = (up,dn) from__ftn rim
a  hub = (pv,nx) from__ftn hub
a  rim = (pv,nx) from__ftn rim

a  rim = rim walk__ftn pv



NB. Certain paths should always form a cycle:
cyclic =. 4 : 'start = (start =. i. # nav__x) walk__x y'
a  ftn cyclic nx,pv,up,dn


NB. We can render fountains as unformatted (non-pretty printed)
NB. s-expressions  using 'ufsx'
a   '()' -: ufsx__ftn''
