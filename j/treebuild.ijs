NB. =treebuild.ijs=

NB. This code is maintained as a literate program with org-babel for emacs.
NB. You can retrieve it in any of three formats:

NB. - [[http://tangentstorm.github.io/apljk/treebuild.ijs.html][a readable html version]]
NB. - [[https://github.com/sabren/b4/blob/master/web/apljk/treebuild.ijs.org][the literate ~.org~ file]]
NB. - [[https://github.com/tangentstorm/b4/blob/master/j/treebuild.ijs][the generated j source code]]
NB. [[file:treebuild.ijs.org::*%3Dtreebuild.ijs%3D][=treebuild\.ijs=:1]]
upfrom =: 3 : 'if. y=_1 do. _1 else. y{tree end.'"0
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
NB. =treebuild\.ijs=:1 ends here
