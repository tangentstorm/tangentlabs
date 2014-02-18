cocurrent'fountains'

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

NB. Basic prototype for an empty fountain:
NB.          u d p n
proto_hub =. 1 1 0 0  NB. The hub is a ring above and below the rim.
proto_rim =. 0 0 1 1  NB. The rim is a ring above and below the hub.

NB. constructor
Fountain =: (proto_hub ,: proto_rim)"_

NB. -- formatting as s-expressions --
NB. ufsx : unformatted (i.e, non-pretty printed) s-expressions:
ufsx =: '()'"_



NB. examples / test cases
NB. ----------------------------------------------------------
a =. assert"0


NB. We can create a fountain simply by invoking the constructor:
ftn =. Fountain''

NB. u d p n
a   1 1 0 0 -: 0 { ftn  NB. initial hub
a   0 0 1 1 -: 1 { ftn  NB. initial rim


NB. We can render fountains as unformatted (non-pretty printed)
NB. s-expressions  using 'ufsx'
a   '()' -: ufsx ftn

