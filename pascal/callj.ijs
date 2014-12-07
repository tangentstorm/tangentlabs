
NB. load main profile.ijs that j uses
18!:4<'z'  NB. set current locale
BoxForm =: 0
BINPATH=:'/usr/home/michal/ver/j/j/bin'
ARGV=:,<'j'

NB. next line is a kludge, compensating for lack of
NB. ~system/defs/*defs_freebsd_64.ijs
NB. UNAME=:'Linux'[IFRASPI=:0
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
fg =: [: cw '|',]
bg =: [: cw '|!',]
reset=: [: cw '|!k|w'"_
immex =: [: (9!:29) 1: [ 9!:27 NB. schedule y:str for immediate execution
import=: coinsert@require


cc'kbd'
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


NB. -- startup --
cc'base'
chdir'../j'

go =: 3 : 0
  cc'base'
  load'cursor.ijs'
  run__cur''
)

gojmf =: 3 : 0
  import'jmf' [ JMF=:'test.jmf'
  if. -. # fdir JMF do. createjmf JMF;1024 end.
  map_jmf_ 'jmf';JMF
)
