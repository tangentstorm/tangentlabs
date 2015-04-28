NB. debug on
NB. (13!:0) 1

NB. load main profile.ijs that j uses
18!:4<'z'  NB. set current locale
BoxForm =: 0
BINPATH=:'/usr/home/michal/ver/j/j/bin'
ARGV=:,<'j'

0!:0 <BINPATH,'/profile.ijs'

NB. -- startup --

UserFolders_j_ =: UserFolders_j_, 'Syn';jpath'~/s'
require'~Syn/startup.ijs'
require'~/l/j/cwio.ijs'
chdir'../j'
