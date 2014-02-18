cocurrent'fountains'

NB. Fountains for J.
NB. ------------------------------------------------------------
NB. A fountain is a type of cyclic graph. It resembles a tree
NB. but contains no null pointers, and can be navigated easily
NB. in any direction. In particular, there is a loop from the 
NB. top of the tree to the bottom.

NB. In this implementation, fountains are structured as tables
NB. with four columns, representing the four directions in which
NB. we can traverse the structure. The names of the directions
NB. are "up, down, previous, and next".
'up dn pv nx' =: i.4

NB. A fountain contains a minimum of two nodes. Node 0 is 
NB. called the 'hub', and is similar to the root of a tree.
NB. Node 1 is called the 'rim', and it models a doubly linked
NB. list containing the leaves of the tree.
'hub rim' =: i.2

at  =: 0
len =: 0

NB. Basic prototype for an empty jump tree:
NB.        u d p n
pro_hub =. 1 1 0 0  NB. The hub is a ring above and below the rim.
pro_rim =. 0 0 1 1  NB. The rim is a ring above and below the hub.

Fountain =: (pro_hub ,: pro_rim)"_



NB. ufsx : unformatted (i.e, non-pretty printed) s-expressions:
ufsx =: '()'"_



NB. examples / test cases
NB. ----------------------------------------------------------
a =. assert"0


NB. We can create a fountain simply by invoking the constructor:
ftn =. Fountain''
a  pro_hub -: 0 { ftn
a  pro_rim -: 1 { ftn


NB. We can render fountains as unformatted (non-pretty printed)
NB. s-expression  using 'ufsx'
a   '()' -: ufsx Fountain''

