NB. a small rpn calculator language in j.

NB. transform verbs so they operate on a stack.
dy =: 1 : '}:@}: , {:@}: u {:'  NB. dyadic stack op.   ex: +dy 0 1 2 3 -> 0 1 5
mo =: 1 : '}: , [: u {:'        NB. monadic stack op.  ex: >: mo 0 1 2 -> 0 1 3

NB. split a string on spaces to make words.
ws =: [: <;._1 ' '&,

NB. keyword list. NOTE: final space maps '' to ] to allow spaces.
kw =: (ws '+ - * / % ^ inc dup drop ')

NB. word list and lookup function
lu =: (kw & i. @ < @ ,)

NB. operation lookup. ex:  1 '+'op 2   -> 3
op=: 1 : '(+ dy)`(- dy)`(* dy)`(% dy)`(| dy)`(^ dy)`(>: mo)`(,~ mo)`((0:$]) mo)`(] mo)`_: @.(lu m)'

NB. the full interpreter pushes number to the stack and uses 
rpn =: ('' & $:) : (4 :'for_w. ws y do. if. _=n=._". >w do. x=.(>w) op x else. x=. x,n end.end.')
