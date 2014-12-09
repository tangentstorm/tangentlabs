NB. load main profile.ijs that j uses
18!:4<'z'  NB. set current locale
BoxForm =: 0
BINPATH=:'/usr/home/michal/ver/j/j/bin'
ARGV=:,<'j'

NB. next line is a kludge, compensating for lack of
NB. ~system/defs/*defs_freebsd_64.ijs
NB. UNAME=:'Linux'[IFRASPI=:0
0!:0 <BINPATH,'/profile.ijs'

NB. -- startup --
require'../j/startup.ijs'
require'../j/cwio.ijs'
chdir'../j'
