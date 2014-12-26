doubles =: (,. +:) i.5 NB. dyadic relation y=2*x, restricted to i.5
squares =: (,. *:) i.5 NB. dyadic relation y=x^2, restricted to i.5

NB. operators for binary relations
V =: converse =: |."1 : [:
U =: union    =: [: : ,
W =: width    =: {. @: (#"1) : [:
H =: height   =: # : [:
X =: cross    =: [: : ,/@(,"1/)

NB. a (ak,bk) J b ->  select * from a X b where (ak{a)=(bk{b)
NB. (as a convenience, drop the second copy of the joined field.)
J =: join =: 1 : 0
  [:
:
  ko =. m + 0, W x                   NB. key offsets for the join
  rp =. (#~ [: =/"1 ko {"1 ]) x X y  NB. 'where' part (restricted product)
  rp {"1~ (i.@W"1 {. rp) -. }."1 ko  NB. remove 2nd copy
)


NB. example tables to work with
NB. ----------------------------
t0 =:(0;'iverson'),(1;'van rossum'),(2;'wirth'),:(3;'moore')

read =: ". @ > @ <;._2

t1 =: read 0 : 0
0;0;'apl'
1;0;'j'
2;1;'python'
3;2;'pascal'
4;2;'modula-2'
5;2;'oberon'
6;3;'forth'
7;3;'colorforth'
)


NB. example: query for a particular row
pasIn2 =: #~ (<'pascal') = 2&{"1
pasIn2 t1  NB. returns the row. (3;2;'pascal')


NB. example: map creators to languages
1 3 {"1 t0 0 1 J t1

