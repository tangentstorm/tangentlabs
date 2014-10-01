NB. 'digits in base y'
NB.  dyad: count to y^x in base y. (x digits each)
NB. monad: count to y^y in base y. (y digits each)
dib =: $:~ : ($ #: i.@^)

NB. normalize array. (in the relational database sense).
NB. replaces each distinct item with a number, which gets reused for duplicates
norm =: ,@:I.&.|:@=
assert 0 1 2 1 2 1 -: norm 'banana'

NB. all partions for y  items
parts =: [: ~. norm"1 @ dib

NB. example: group (parts 5) by the first 3 items (parts 3)
(([: ~. {."1) ,: ({."1 </. ;@}."1)) k=.( 3&{. ; _2&{.)"1 (parts 5)

(0 : 0) the result:
┌─────┬─────┬─────┬─────┬─────┐
│0 0 0│0 0 1│0 1 0│0 1 1│0 1 2│
├─────┼─────┼─────┼─────┼─────┤
│0 0  │0 0  │0 0  │0 0  │0 0  │
│0 1  │0 1  │0 1  │0 1  │0 1  │
│1 0  │0 2  │0 2  │0 2  │0 2  │
│1 1  │1 0  │1 0  │1 0  │0 3  │
│1 2  │1 1  │1 1  │1 1  │1 0  │
│     │1 2  │1 2  │1 2  │1 1  │
│     │2 0  │2 0  │2 0  │1 2  │
│     │2 1  │2 1  │2 1  │1 3  │
│     │2 2  │2 2  │2 2  │2 0  │
│     │2 3  │2 3  │2 3  │2 1  │
│     │     │     │     │2 2  │
│     │     │     │     │2 3  │
│     │     │     │     │3 0  │
│     │     │     │     │3 1  │
│     │     │     │     │3 2  │
│     │     │     │     │3 3  │
│     │     │     │     │3 4  │
└─────┴─────┴─────┴─────┴─────┘
)
