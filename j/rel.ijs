
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
