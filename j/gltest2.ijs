NB. animation test
NB. draws a bunch of random colored rectangles on every frame

require'graph' [ coinsert'jgl2'

nboxes =: 100 

gfx_g_paint =: verb define
 for_i. i.100 do.
   glrgb i { colors
   glbrush''
   glrect i { boxes
 end.
)

step =: verb define
  update''
  glsel'g'
  glpaintx''
)

NB. this callback doesn't actually get called. :/
NB. ---------------------------------------------
gfx_close =: verb define
  sys_timer_z_=:]
  echo 'close'
  wd 'timer 0;'
  codestroy''
)

NB. update on every tick
NB. ----------------------------------------------------
NB. We rebuild the scene here rather than in gfx_g_paint
NB. because that runs on other events like mouse clicks
NB. or dragging the window, and we want this to run at
NB. a constant speed. 
update =: verb define
  colors =: ? (nboxes, 3) $ 255
  boxes  =: ? (nboxes, 4) $ 500 500 150 150
  EMPTY
)

NB. -- run it! ----------------
update''
sys_timer_z_ =: ('step_',(>coname''),'_')~
wd 0 : 0
  pc gfx closeok; minwh 600 600;
  cc g isigraph; pas 0 0; pshow;
  timer 50;
)
