NB. a basic cursor class, with support for text terminal display

cocurrent'ansi'
load'ansi.ijs'

coclass'Cursor'

create =: verb define
  here =: 0
  setdata y
)

setdata =: verb define
  data =: y [ lo =: 0 [ hi =: #y
  nudge 0
)

NB. "tab stops" for each item, since they may have different lengths
stops =: {:@$@":\

show =: verb define
  echo data
  'c w' =. (here&{ , {:) 0,<: stops data
  ' ^'{~ c = i. 1 >. w
)

nudge =: verb define
  here=: hi <. lo >. here + 1$y
)


coclass 'AnsiCursor'
coinsert 'ansi'
coinsert 'Cursor'

show =: verb define
  NB. TODO: just inherit this and modify the last line.
  echo data
  'c w' =. (here&{ , {:) 0,<: stops data
  ((fg'K'),reset,~]) (u:' ',u:8593) {~ c = i. 1+ w
)

cocurrent'base'
coinsert'ansi'
Cursor =: conew&'Cursor'
AnsiCursor =: conew&'AnsiCursor'

cur =: AnsiCursor i.10
