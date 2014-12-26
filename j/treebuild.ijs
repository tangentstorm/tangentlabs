
tree =: $0   NB. stores the links to parents.
data =: $0   NB. stores the actual data items.
path =: $0   NB. the stack of parent nodes.
here =: _1   NB. the current parent node.

emit =: monad define "0
  tree =: tree, here
  data =: data, y
  tree
)

node =: monad define "_
  path =: path, here
  here =: <: # tree
  tree
)

done =: monad define "_
  here =: {: path
  path =: }: path
  tree
)

drop =: monad define "_
  data =: }: data
  tree =: }: tree
  tree
)

goto =: monad define "_
  path =: path, here
  here =: y
  tree
)
upfrom =: 3 : 'if. y=_1 do. _1 else. y{tree end.'
dnfrom =: 3 : 'if. 0=#y do. $0 else. I. +./"2 tree ="1 0 ;y end.'"1
above =: (_1 -.~ }.)&(upfrom f.^:a:)"0
below =: 13 : '; }. dnfrom each ^:a: < y'
depth =: #@above
treet =: 3 : '(i.#tree),.tree,.data' NB. tree table :)
index =: 3 : '(i.#tree)'
reset =: verb define
  tree =: path =: data =: $ >: here =: _1
)
tree0 =: verb define
  emit i. 5
  node''
  emit 44 45 46
  done''
  emit 5 6
  node''
  emit 60 61 62
  done''
  goto 4
  emit 44
  done''
  goto data i. 61
  emit 610 611
  done''
)

rsx =: (node`done`emit)@.('()' & i.)"0  NB. 'read s-expression'

