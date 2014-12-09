NB. misc startup routines
cocurrent'z'

cc =: 18!:4@(<^:(L. < *@#)) ::(18!:5)  NB. cocurrent :: coname f.
immex =: [:(9!:29)1: [9!:27 NB. schedule y:str for immediate execution
import=: coinsert@require
doAt=: 2 : '(u n{y) n } y NB. apply u at indices given by n'

ord=: a.i.]
chr=: ord^:_1
ctrl=: (_64 + ])&.ord

getcwd=:1!:43
chdir =:1!:44

go =: 3 : 0
  cc'base'
  load'cursor.ijs'
)

gojmf =: 3 : 0
  import'jmf' [ JMF=:'test.jmf'
  if. -. # fdir JMF do. createjmf JMF;1024 end.
  map_jmf_ 'jmf';JMF
)
