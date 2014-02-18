coclass 'Fountain'
NB. Fountains for J.
NB. ------------------------------------------------------------
NB. Fountains are a type of cyclic graph. They resembles trees
NB. but contain no null pointers, and can be navigated easily
NB. in any direction. In particular, (almost) all links are
NB. bi-directional, and there is a link connecting the top of
NB. the structure to the bottom.

NB. In this implementation, fountains are structured as four
NB. parallel arrays, representing the four directions in which
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
  nav_up =: nav_dn =: 1 0
  nav_pv =: nav_nx =: 0 1
  0 return.
)

NB. destructor
destroy =: monad define
  codestroy ''
)

NB. basic navigation and metadata
NB. ------------------------------------------------------------

NB. nav :: (up,dn,pv,nx:nid) <- nid
nav =: monad define "0
  (y { nav_up), (y { nav_dn), (y { nav_pv), (y { nav_nx)
)

NB. len :: int <- any
len =: monad define "_
  # nav_up  NB. any of the links would work
)

NB. from :: nid <- dir <- nid
NB. (nid means 'node id'. e.g, 0 for the hub)
from =: dyad define"0 0
select. x
case. up do. y { nav_up      case. dn do. y { nav_dn
case. pv do. y { nav_pv      case. nx do. y { nav_nx
end.
)

NB. walk :: [nids] <- start:[nid] <- path=(dir,dir,dir...)
NB. monadic case starts walking from the hub
walk =: verb define "0 1
  0 $: y
:
  for_step. ;y do. x =. step from x end.
)

NB. tools for updating

get =: 1 : '(<m) { y'
put =: 2 : 'n (<m) } y'


NB. -- adding data : insert, append ----------------------------

NB. link_XX :: () <- nid <- nid
link_up =: (dyad def 'nav_up =: y x } nav_up')"0 0
link_dn =: (dyad def 'nav_dn =: y x } nav_dn')"0 0
link_pv =: (dyad def 'nav_pv =: y x } nav_pv')"0 0
link_nx =: (dyad def 'nav_nx =: y x } nav_nx')"0 0

NB. ins_nx :: new <- old:nid <- new:nid
ins_nx =: dyad define "0 0
  if. y ~: nx from y
  do. echo 'can only ins singletons for now' throw. end.

  NB. first, preserve the old links:
  y link_nx  (nx from x)  [  (nx from x) link_pv y

  NB. then create the new ones:
  y link_pv  x  [   x link_nx  y
)

NB. -- adding structure : rings --------------------------------
NB. Rings are just circular linked lists. Each data node in the
NB. fountain is connected to its siblings in a ring. Each ring
NB. consists of two nodes: a hook (which holds its place in the
NB. parent ring) and a clasp (which holds the ends of the child
NB. ring together).

NB. insert_ring :: (hook,clasp:nid) <- parent:nid
insert_ring =: monad define "0
  'h c' =: 0 1 + len''
  nav_up =: nav_up, h, h
  nav_dn =: nav_dn, c, c
  nav_pv =: nav_pv, h, c
  nav_nx =: nav_nx, h, c
  h ins_nx y
  h, c return.
)

NB. is_clasp :: bit <- nid
NB. a clasp is its own child but not its own parent.
is_clasp =: (( [ = dn from ] ) :[:)"0

NB. is_hook :: bit <- nid
NB. a hook is its own parent but not its own child.
is_hook  =: (( [ = up from ] ) :[:) "0

NB. -- formatting as s-expressions --
NB. ufsx : unformatted (i.e, non-pretty printed) s-expressions:
ufsx =: '()'"_



NB. test cases and examples
NB. ----------------------------------------------------------
cocurrent 'FountainTest'
coinsert 'Fountain'
a =. *./ & assert"0

NB. We can create a fountain simply by invoking the constructor:
ftn =. '' conew 'Fountain'

NB. Here is how a new fountain should look:
NB. u d p n
a   1 1 0 0 -: nav__ftn 0    NB. Node 0 is the hub, a ring up/dn from the rim.
a   0 0 1 1 -: nav__ftn 1    NB. Node 1 is the rim, a ring up/dn from the hub.
a   2 = len__ftn''           NB. there are no other nodes

a  rim = (up,dn) from__ftn hub  NB. ie, rim is both up and dn from hub
a  hub = (up,dn) from__ftn rim  NB. (these are only true for empty fountains)
a  hub = (pv,nx) from__ftn hub
a  rim = (pv,nx) from__ftn rim

a  rim = rim walk__ftn pv,pv,pv,pv



NB. tests for adding data
NB. ------------------------------------------------------------

NB. tests for adding rings
NB. ------------------------------------------------------------
ftn =. ('' conew 'Fountain') [ (destroy__ftn'')

'h c' =. insert_ring__ftn hub       NB. rings consist of two nodes
a  4 = len__ftn                     NB. both should be added to ftn.
a  h = up from__ftn h               NB. node h is its own parent.
a  is_hook__ftn h                   NB. .. which marks it as a hook.
a  c = dn from__ftn c               NB. node c is its own child.
a  is_clasp__ftn c                  NB. .. which marks it as a clasp.

a  hub = (pv,nx) from__ftn h        NB. h should be a sibling of the hub
a  h = (pv,nx) from__ftn hub        NB. .. and vice versa.
a  c = (pv,nx) from__ftn c          NB. but the clasp has no siblings yet.

NB. tests for paths that should always be cycles
NB. ------------------------------------------------------------
nodes =. i. len__ftn''
a  nodes = nodes walk__ftn nx, pv
a  nodes = nodes walk__ftn pv, nx


NB. Other paths are cycles except for clasps.

NB. TODO:
NB. structural =. (is_hook__ftn +. is_clasp__ftn) nodes
NB. others =. nodes -. structural
NB. a  others = others walk__ftn nx,pv,up,dn


NB. We can render fountains as unformatted (non-pretty printed)
NB. s-expressions  using 'ufsx'
a   '()' -: ufsx__ftn''
