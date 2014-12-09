import 'list.ijs'

NB. a basic cursor class, with support for text terminal display
coclass'Cursor'

create =: monad define
  data =: List''
  here =: 0
  setdata y
)
setdata =: monad define
  update__data y
  nudge 0
)
ins =: monad define
  here ins__data y
  nudge #y
)
del =: verb define
  del__data here
)
swap =: verb define
  if. -. here e. 0, len__data do. here swap__data here-1 end.
)
dup =: verb define
  if. here > 0 do. setdata (>: ((<: here) = i. # data)) # data end.
)
nudge =: monad define
  lo =: 0 [ hi =: len__data''
  here=: hi <. lo >. here + {.y
)

Cursor_z_ =: conew&'Cursor'

