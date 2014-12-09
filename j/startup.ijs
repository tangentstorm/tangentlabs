NB. this file contains a bunch of words I use to configure my
NB. J environment.
cocurrent'z'

cc =: cocurrent :: coname f.
module =: cocurrent
import =: coinsert [ require

immex =: [:(9!:29)1: [9!:27 NB. schedule y:str for immediate execution

doAt=: 2 : '(u n{y) n } y NB. apply u at indices given by n'

ord  =: a.i.]
chr  =: ord^:_1
ctrl =: (_64 + ])&.ord  NB. ASCII control characters

getcwd=:1!:43
chdir =:1!:44

3 : 0''
  NB. include scratch.ijs if it exists
  NB. (so i have a place to put work-in progress/debug code to run at startup)
  if. fexist '~/l/j/scratch.ijs' do. load '~/l/j/scratch.ijs' end.
)
