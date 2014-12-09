NB. string database
NB.
NB. This module associate strings with numbers, using a
NB. component file to map numbers to strings, and a keyed
NB. file to map the strings to numbers.
NB.
NB. Only one database is used at a time. To select the
NB. database, run:  stringdb'data/strings'
NB.
module 'stringdb'
import 'jfiles'

stringdb =: verb define
  assert #y
  valpath=:y,'.k2s' NB. int → str
  keypath=:y,'.s2k' NB. str → int
  if. -.fexist valpath do. jcreate valpath end.
  if. -.fexist keypath do. keycreate keypath end.
)

s2k =: verb define
  NB. return key corresponding to y:str
  key=.keyread keypath;y  NB. will be boxed if found
  if. key -: _4 do.       NB. not found, so add it.
    key =. y jappend valpath
    key ([[[keywrite keypath;]) y
  else. >key end.
)

k2s =: verb define
  NB. given key y:nat, return corresponding string
  jread valpath;y  NB. will be boxed if found
)
