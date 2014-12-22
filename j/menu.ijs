NB. start on an interactive text-mode menu class
NB.
NB. usage:
NB.
NB.    load 'menu.ijs'
NB.    m =: Menu 'one';'two';'three'
NB.    run__m''
NB.
coclass 'Menu'
import 'cursor' [ load'cwio.ijs'
coinsert'kbd'

create =: monad define
 cur =: Cursor items=:y
)

hl =: verb define
 (cwstr'|)|!r'), y, (cwstr'|(') NB. highlight line with red bg
)

show =: monad define
 cw cls
 0$ cw each hl&.> doAt here__cur items
)

run  =: monad define
 done =. 0
 whilst. -. done do. show''
   select. ch=.rk''
     fcase. 'p' do. case. U_ARROW do. nudge__cur _1
     fcase. 'n' do. case. D_ARROW do. nudge__cur  1
     fcase. ' ' do. case. ENTER   do. done =. 1
     case. 'q'  do. done =. 1
   end.
 end.
 here__cur
)

step =: monad define
)

Menu_z_ =: conew&'Menu'
