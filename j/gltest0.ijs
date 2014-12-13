NB.
NB.  demo of low level custom graphics in j803 (jqt)
NB.

cocurrent'gltest0'
coinsert 'jgl2'[load 'graph'


setup=: 0 : 0
  pc w closeok; pmove 700 0 640 480;
  cc g isidraw;
  pas 0 0;
)
gltest0 =: 3 : 0            NB. initialization
  if. (nameclass<'ready')<0 do. ready =: 1 [ wd setup end.
  wd'pshow'
)


w_g_char=: 3 : 0           NB. keyboard handler

  NB. draw a rectangle in upper left:
  glpaint@glrect 0 0 50 50 [ glbrush@glrgb ?3$256

  NB. print the key that was pressed:
  echo a.i.sysdata

  NB. stamp a random bitmap to the screen:
  glpaint@glpixels 50 50 50 50 , ?(50*50)$ 16bfffffffff
)


w_g_mmove=: 3 : 0          NB. mouse move handler

  echo 'msx msy gw gh mbl mbr ctrl shift'=:8{.0&".sysdata

  NB. leave a (disconnected) white pixel after each mouse move.
  glpaint@glpixel msx,msy [ glpen [ glrgb WHITE
)


gltest0''

