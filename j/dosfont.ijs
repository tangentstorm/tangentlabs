load 'viewmat'
ord  =: 256 #: a. i. ]
bits =: _8&{.#:]
fnt  =: fread 'r:\old\pascal.cvs\inc\sabren.fnt'

NB. this shows the letter 'k' as a graphic
viewmat (ord 'k') { >256 16 $(_8&{.#:) each ord  fnt

NB. every 16 makes a char
chars =: _16<\ord fnt
bits =: (_8&{. #:)"0 
maps =: bits > chars    NB. 256 16 18

16 16& $ <"2 maps NB. 16 x 16 boxed

NB. i don't know how to get this into bitmap format 
NB. even though it's basically the same as the tetris thing i made.
NB. this shows 'abc' as ascii:
;/>'.x'{~ >(ord 'abc') { maps


