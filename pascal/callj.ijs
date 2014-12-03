
NB. load main profile.ijs that j uses
18!:4<'z'  NB. set current locale
BoxForm =: 0
BINPATH=:'/usr/home/michal/j701/bin'
ARGV=:,<'j'
0!:0 <BINPATH,'/profile.ijs'

cocurrent'z'
cc =: 18!:4@(<^:(L. < *@#)) ::(18!:5)  NB. cocurrent :: coname f.

NB. read/write from keyboard
rl=:[: (1!:1) 1:
wr=:0$(1!:2)&2   NB. &2 selects 'screen', so callj intercepts
rk=: 3 : 0
  wr 11{a. NB. ^K
  ,":rl''  NB.  TODO: fix this security hole.
)

ord=: a.i.]
chr=: ord^:_1
ctrl=: (_64 + ])&.ord
cwtrg=: chr _64 + ord'F' NB. trigger character for terminal stuff.
cwstr=: ('|',cwtrg) charsub ,"1
cw =: wr@cwstr
cls=:cwstr'|$'
getcwd=:1!:43
chdir =:1!:44

chdir'../j'

go =: 3 : 0
  cc'base'
  load'cursor.ijs'
  run__cur''
)


cc'kbd'
U_ARROW =:0 72
D_ARROW =:0 80
L_ARROW =:0 75
R_ARROW =:0 77
PGUP    =:0 73
PGDN    =:0 81
ENTER   =:, 13
TAB     =:,  9
CTRL_N  =:, 14
CTRL_P  =:, 16
CTRL__  =:, 31 NB. control +  '-'  (i use this for undo on dvorak)

cc'base'
