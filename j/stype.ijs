NB. stype (symbolic type)
NB. stype y converts result of (3!:0 y) (datatype) to a simpler format:

    0 1 2 4 8 16 32 64 128 256 512 1024 2048 4096 8192 16384 32768 65536 131072
t=.'? n t n n n  b  n  n   ?   ?   n    t    n    n    n     b     s     t'
s=.'SYM TXT NUM BOX UNK'=: s:' symbol text number boxed unknown'
stype=: s {~ 'stnb?' i. (; ;: t) {~ [: >: 2^.(3!:0)
