NB. ascii character table
load'tangentstorm/j-kvm/vt'
coinsert 'vt'

sq =. ''''
rows01 =. tolower 2 48 $, (sq,'  '),~,' ^' 1&|.@,"1 0 a.{~64+i.31
rows27 =. 6 48$' ^?',~,' ',.~sq,"1 0 a.{~33+i.95
rows8f =. toupper 8 48 $,' ',.~,/hfd 128+i.8 16


echo <'ascii character table (b4a syntax)'
echo
([: puts (CR,LF),~])"1 rows01,rows27,rows8f
