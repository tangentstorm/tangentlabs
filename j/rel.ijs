doubles =: (,. +:) i.5 NB. dyadic relation x=2*y, restricted to i.5
squares =: (,. *:) i.5 NB. dyadic relation x=y*y, restricted to i.5

NB. operators for binary relations
cv =: converse =: |."1 : [:
U =: union   =: [: : ,
W =: width =: {. @: (#"1) : [:
H =: height =: # : [:

X =: product =: [: : ,/@(,"1/)
J =: join =: 1 : ' (#~ =/"1 (0, W y) + m) { ])    x X y'

NB. a (ak,bk) J b ->  select * from a X b where (ak{a)=(bk{b)
NB. (as a convenience, drop the second copy of the joined field.)
J =: join =: 1 : 0
  [:
:
  ko =. m + 0, W x                   NB. key offsets for the join
  rp =. (#~ [: =/"1 ko {"1 ]) x X y  NB. 'where' part (restricted product)
  rp {"1~ (i.@W"1 {. rp) -. }."1 ko  NB. remove 2nd copy
)


NB. tables to work with
NB. -------------------------
t1 =:(0;'iverson'),(1;'van rossum'),(2;'wirth'),:(3;'moore')


t2=.(0;0;'apl'),(1;0;'j'),(2;1;'python'),(3;2;'pascal'),(4;2;'modula-2'),(5;2;'oberon'),(6;3;'forth'),:(7;3;'colorforth')

read =. ". @ > @ <;._2

t3 =. read 0 : 0
0;0;'apl'
1;0;'j'
2;1;'python'
3;2;'pascal'
4;2;'modula-2'
5;2;'oberon'
6;3;'forth'
7;3;'colorforth'
)


NB. query for a particular row
pasIn2 =: (] #~ (<'pascal') = 2&{"1)
pasIn2 t3  NB. returns the row.


NB. cross join
xj =: ,/ & ( [ ,/"1/ ] )


NB. inner join
NB. -------------------------
ij =: ((0&{ = 3&{)"1 # ]) ,/ t1 ,/"1/ t2
