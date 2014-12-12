NB. draws a draggable square and displays its coordinates.

require'graph'[coinsert'jgl2'

GFX=: 0 : 0
 pc gfx closeok;
 minwh 640 480;cc g isigraph;
 pas 0 0; pshow
)

gfx_run=: 3 : 0
 wd GFX
)

toggle=: _55 200 200[drag=:0[pxy=:200 200[pwh=:150 150

gfx_g_paint=: 3 : 0
 glrgb 255 0 0 + toggle * drag
 glbrush''
 glrect (pxy,pwh)
 gltextxy 20 20
 gltext ":pxy
)

mxy=: 3 :0
 2{. 0&". sysdata
)

gfx_g_mbldown=: 3 : 0
 oxy=: mxy''
 if. *./(>&0,<&pwh)oxy-pxy do. glpaint''[drag=: 1 end.
)

gfx_g_mblup=: 3 : 0
 drag=: 0
 glpaint''
)

gfx_g_mmove=: 3 : 0
 if. -. drag do. return. end.
 pxy=: pxy+oxy-~nxy=. mxy''
 glpaint''
 oxy=: nxy
)

gfx_run''
