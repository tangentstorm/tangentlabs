NB. a simple memory-mapped graph database
cc'base' [ load 'mvars.ijs'

enum'rChild rType'
mvar'SUB REL OBJ LOG'
'`sub rel obj log'=:('SUB'G)`('REL'G)`('OBJ'G)`('LOG'G)

incoming =: sub = ]
outgoing =: obj = ]
children =: (#~ rChild=]{rel) @ outgoing
