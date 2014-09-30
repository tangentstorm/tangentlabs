NB. 'digits in base y'
NB.  dyad: count to y^x in base y. (x digits each)
NB. monad: count to y^y in base y. (y digits each)
dib =: $.~ : ($ #: i.@^)

NB. normalize array. (in the relational database sense).
NB. replaces each distinct item with a number, which gets reused for duplicates
norm =: ,@:I.&.|:@=
assert 0 1 2 1 2 1 -: norm 'banana'

NB. all partions for y  items
parts =: [: ~. ([: >./ norm)"1 @ dib
