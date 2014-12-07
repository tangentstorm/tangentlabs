NB. a basic cursor class, with support for text terminal display


coclass'List'

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
  update (y {. value), y + x }.value
)
len =: verb define
  # value
)
swap =: verb define
  (2|.\y) swap y  NB. swap 0 1 2 3 →  1 0 3 2 swap 0 1 2 3
:
  update (y{value) x } value
)
List_z_ =: conew&'List'


coclass'Cursor'

create =: monad define
  data =: List''
  here =: 0
  setdata y
)
setdata =: monad define
  update__data y [ lo =: 0 [ hi =: #y
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
  here=: hi <. lo >. here + {.y
)

coclass 'Editor'
coinsert 'Cursor kbd'

NB. "tab stops" for each item, since they may have different lengths
stops =: {:@$@":\

show =: verb define
  boxes =. value__data
  wr boxes [ cw'|$|g'                     NB. draw the boxed items
  'c w' =. (here&{ , {:) 0,<: stops boxes
  cw '|K', (u:' ',u:8593) {~ c = i. 1+ w  NB. draw arrow
  cw '|B'
  try. wr ". ; }. ,(<,' '),. boxes catch. (cw'|r ')[wr(13!:12)'' end.
  cw '|w'
)

prompt =: verb define
  cw y
  cw'|)|!k|33'
  r =. ;: rl ''
  r [ cw '|('
)

run =: verb define
  done =. 0
  while. -. done do.
    show''
    select. ch =. a.{~".rk''
      case. L_ARROW;'<';'b';ctrl'B' do. nudge _1
      case. R_ARROW;'>';'f';ctrl'F' do. nudge  1
      case. 'i' do. ins prompt'|winsert:'
      case. 'x' do. del''
      case. 'd' do. dup''
      case. 't' do. swap''
      case. 'q' do. done=.1
    end.
  end.
)


cocurrent'base'
coinsert'ansi'

Cursor_z_ =: conew&'Cursor'
Editor_z_ =: conew&'Editor'

ed  =: Editor ;:'i. 3 3'

immex 'run__ed _'

