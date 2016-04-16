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

gfx_timer =: verb define
  update''
  glsel'g'
  glpaintx''
)

gfx_cancel =: verb define
  smoutput 'closed'
  wd 'ptimer 0; pclose;'
)

update =: verb define
  NB. We rebuild the scene here rather than in gfx_g_paint
  NB. because that runs on other events like mouse clicks
  NB. or dragging the window, and we want this to run at
  NB. a constant speed.
  colors =: ? (nboxes, 3) $ 255
  boxes  =: ? (nboxes, 4) $ 500 500 150 150
  EMPTY
)

update''
wd 0 : 0
  pc gfx escclose; minwh 600 600;
  cc g isigraph; pas 0 0; pshow;
  ptimer 50;
)
