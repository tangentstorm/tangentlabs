coclass 'List'
doc =: 'A general purpose list class.'

create =: monad define
  update y
)
update =: monad define
  value=:y NB. replace all values
)
get =: monad define
  y { value
)
ins =: dyad define
  update x ({., y, }.) value
)
del =: verb define
  1 del y
:
  update (y {. value), (y + x) }. value
)
len =: verb define
  # value
)
swap =: verb define
  (2|.\y) swap y  NB. swap 0 1 2 3 →  1 0 3 2 swap 0 1 2 3
:
  update (y{value) x } value
)

List_z_=:conew&'List'
