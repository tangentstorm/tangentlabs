NB. a basic cursor class, with support for text terminal display


coclass'Cursor'

create =: monad define
  here =: 0
  setdata y
)

setdata =: monad define
  data =: y [ lo =: 0 [ hi =: #y
  nudge 0
)

ins =: monad define
  setdata here ({., y, }.) data
  nudge #y
)

del =: verb define
  setdata here ({. , }.@}.) data
)

swap =: verb define
  if. -. here e. 0, #data do.
    setdata ;0 2 1 3 /:~ here (split&.(_1|.])@{. , split@}.) data
  end.
)

dup =: verb define
  if. here > 0 do. setdata (>: ((<: here) = i. # data)) # data end.
)

NB. "tab stops" for each item, since they may have different lengths
stops =: {:@$@":\

show =: verb define
  wr data
  'c w' =. (here&{ , {:) 0,<: stops data
  ' ^'{~ c = i. 1 >. w
)

nudge =: monad define
  here=: hi <. lo >. here + {.y
)


cocurrent'ansi'
NB.load'ansi.ijs'
fg =: [: cw '|',]
reset=: [: cw '|!k|w'"_

coclass 'AnsiCursor'
coinsert 'ansi'
coinsert 'Cursor'

show =: verb define
  wr data [ cw'|$|g'                      NB. draw the data
  'c w' =. (here&{ , {:) 0,<: stops data
  cw '|K', (u:' ',u:8593) {~ c = i. 1+ w  NB. draw arrow
  cw '|B'
  try. wr ". ; }. ,(<,' '),. data catch. (cw'|r ')[wr(13!:12)'' end.
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
      case. '<';'b';ctrl'B' do. nudge _1
      case. '>';'f';ctrl'F' do. nudge  1
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

Cursor =: conew&'Cursor'
AnsiCursor =: conew&'AnsiCursor'

cur =: AnsiCursor ;:'i. 3 3'

imx =: [: (9!:29) 1: [ 9!:27
imx 'run__cur _'

