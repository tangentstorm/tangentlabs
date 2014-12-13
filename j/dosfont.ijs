NB. dos (vga) font viewer.
NB. vga fonts were 256*16

load 'graph' [ coinsert 'jgl2'
ord  =: 256 #: a. i. ]
bits =: _8 {.#:

NB. TODO: not sure how to avoid hard-coding this path
fnt  =: fread 'l:/j/ibmvga437.fnt'
assert -.fnt-:_1 NB. you need to change the path to the font. :/

NB. each character is 16 bytes
assert 256 16 8 -: $ maps =: >bits"0 L:0] _16<\ord fnt

chmp=: maps {~ ord
zoom=: 2 # 2 #"0 1 ]  NB. 1 pixel becomes 4


opq =: 16bff000000 NB. opaque mask
red =:   16bff0000 NB. red
fgc =:   16bffcc44 NB. gold

NB. cls : clear screen
NB. ------------------
cls =: glpaint@glfill [ [: glrgb 0 0, 0:


NB. color (x y) cxy text
NB. --------------------
cxy =: adverb define
 [:
:
 bmp =. ,./^:2 chmp _16[\ y
 glpaint@glpixels m, (|.@$,,) opq+x *x:bmp
)
 

demo =: 3 : 0
 wd'pc dosfont closeok; pmove 700 0 640 480;'
 wd'cc g isidraw;'
 wd'pas 0 0; pshow;'
 cls''
 red 16 32 cxy a.
 fgc 16 16  cxy 'hello world'
)

demo''
