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
  NB. Basic prototype for an empty fountain:
  NB.          u d p n
  proto_hub =. 1 1 0 0  NB. The hub is a ring above and below the rim.
  proto_rim =. 0 0 1 1  NB. The rim is a ring above and below the hub.
  nav =: (proto_hub ,: proto_rim)
  0 return.
)

destroy =: verb define
  codestroy ''
)

NB. -- formatting as s-expressions --
NB. ufsx : unformatted (i.e, non-pretty printed) s-expressions:
ufsx =: '()'"_



cocurrent 'FountainTest'
NB. examples / test cases
NB. ----------------------------------------------------------
a =. assert"0


NB. We can create a fountain simply by invoking the constructor:
ftn =. '' conew 'Fountain'

NB. Here is how a new fountain should look:
NB. u d p n
a   1 1 0 0 -: 0 { nav__ftn  NB. node 0 is the proto-hub
a   0 0 1 1 -: 1 { nav__ftn  NB. node 1 is the proto-rim
a   2 = # nav__ftn           NB. there are no other nodes

NB. The path nx,pv,up,dn should always form a cycle
a start = (start=.i.#len__ftn) walk__ftn


NB. We can render fountains as unformatted (non-pretty printed)
NB. s-expressions  using 'ufsx'
a   '()' -: ufsx__ftn''
