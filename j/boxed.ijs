coclass 'BoxEd'
require each ' ' splitstring 'cwio.ijs list.ijs cursor.ijs'
coinsert 'Cursor kbd'
doc =: 'A simple editor for boxed arrays'


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

BoxEd_z_ =: conew&'BoxEd'
