NB. a simple memory-mapped graph database
cc'base' [ load each 'mvars.ijs';'stringdb.ijs'

stringdb mdir,'/nodes.jf'

enum'rType rChild'

3 : 0''
  NB. only declare these mapped variables if they're undefined.
  NB. if the file is already mapped, it'll cause an assertion
  NB. failure. This conditional is just to allow reloading this
  NB. file during development.
  if. _1 = (4!:0)<'SUB' do.
    mvar'SUB REL OBJ ETS'  NB. the table of edges
    '`sub rel obj ets'=:('SUB'G)`('REL'G)`('OBJ'G)`('ETS'G)
  end.
)

incoming =: [: I. obj = ]
outgoing =: [: I. sub = ]
children =: (#~ rChild=]{rel) @ outgoing

nid =: ({.@s2k) :. k2s NB. fetch node id given string value

declare =: verb define
  NB. declare 'sub rel obj' → creates a new edge in the db.
  's r o' =. (+ :: (nid"0@:(;: :: ]))) y
  SUB =: SUB,s [ REL =: REL,r [ OBJ =: OBJ,o
  ETS =: ETS,tsrep 6!:0'' NB. timestamp each entry.
  EMPTY
)

retract =: verb define
  NB. retract'' → removes the most recently created edge.
  SUB =: }:SUB [ REL =: }:REL [ OBJ =: }:OBJ [ ETS =: }:ETS
  EMPTY
)

edges =: verb define
  NB. returns a boxed table of strings, representing the edges.
  if. -.#y do. y=.i.#SUB end.
  >@k2s "0 L:0(y{SUB);(y{REL);(y{OBJ)
)
