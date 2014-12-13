NB. implements a 2d grid cursor

cocurrent'glgrid'
coinsert 'jgl2'[load 'graph'

cxy =: 0 0
key =:''
nudge =: 3 : 0
  cxy =: 10|cxy+y
)
win_g_char=: 3 : 0           NB. keyboard handler 
 select. key =: a.i.sysdata
  case. 239 160 146 do. nudge-1 0 NB. left
  case. 239 160 147 do. nudge-0 1 NB. up
  case. 239 160 148 do. nudge+1 0 NB. right
  case. 239 160 149 do. nudge+0 1 NB. down
 end.
)

padding=:4 4
GOLD=:16bff 16bd7 0

textbox=: 3 : 0
 (glfont,glfontextent)'"consolas" 11'
 'xy fg bg text' =: y
 gltextcolor glrgb BLACK
 glpen 0 [ glrgb BLACK [ glbrush glrgb bg
 glrect xy, r=:(+:padding)+glqextent text
 gltextxy padding+xy
 gltext text
 r return.
)

win_g_paint=: 3 : 0
 txy=.(left=.5 0)+(top=.0 5) 
 for_j. i.10 do. for_i. i.10 do.
  bg=.>((i,j)-:cxy){WHITE;GOLD
  txy =. txy + 1 0 * wh=.textbox txy;BLACK;bg;":i,j
 end. txy =. left + 0 1 * txy + wh end.
 glpaint''
)

main=: 3 : 0
 try. wd 'psel win'
 catch.
   wd 'pc win closeok; pmove 700 0 640 480; pas 0 0'
   wd 'cc g isigraph; pshow'
   wd 'pn "glgrid demo"'
  end.
)

main''

