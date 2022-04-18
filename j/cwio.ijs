NB. ==== screen i/o ===============================
NB.
NB. NOTE: this stuff currently only works when using
NB. ../pascal/callj.pas as the J frontend.
NB.
NB. i am keeping this around for my own personal
NB. reference, but it is almost completely superceded by:
NB.
NB.   http://github.com/tangentstorm/j-kvm/
NB.
cocurrent 'cwio'

NB. -- writing to screen -------------------------
wr=:0$(1!:2)&2   NB. &2 selects 'screen', so callj intercepts
cwtrg=: chr _64 + ord'F' NB. trigger character for terminal stuff.
cwstr=: ('|',cwtrg) charsub ,"1
cw =: 0 0 $ wr@cwstr
cls=:cwstr'|$'
fg =: [: cw '|',]
bg =: [: cw '|!',]
reset=: [: cw '|!k|w'"_
goxy =: cwstr@:('|@',])@:('0'"_^:(' '=])"0)@(2":])
nval =: ".@(#~ ' _0123456789' e.~ ])

NB. -- reading from keyboard ---------------------
rl=: [: (1!:1) 1:  NB. readline
rk=: 3 : 0
  wr 11{a. NB. ^K
  a.{~ nval rl''
)

NB. -- keyboard contants -------------------------
cocurrent'kbd'
U_ARROW =:0 72{a.
D_ARROW =:0 80{a.
L_ARROW =:0 75{a.
R_ARROW =:0 77{a.
PGUP    =:0 73{a.
PGDN    =:0 81{a.
ENTER   =:, 13{a.
TAB     =:,  9{a.
CTRL_N  =:, 14{a.
CTRL_P  =:, 16{a.
CTRL_DASH=:, 31{a. NB. control +  '-'  (i use this for undo on dvorak)

