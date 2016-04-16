coclass 'webworld'
coinsert 'd3'

NB. require 'graphics/d3'

NB. ---------- web stuff ----------------------------------------------

CSS =: 0 : 0
*{color:#333;font-family:verdana;font-size:12pt;}
)

text =: 0 : 0
)

JSSRC=: 0 : 0
d3.v3.min.js
)
JSSRC=: ;(<HPATH) , each (<;._2 JSSRC) ,&.> (<LF)
JSSRC=: JSSRC,'http://code.jquery.com/jquery-2.0.3.min.js',LF

HBS =: 0 : 0
'<script src="~addons/ide/jhs/js/jquery/jquery-2.0.3.min.js"></script>'
'<script src="~addons/ide/jhs/js/d3/d3.v3.min.js"></script>'
      text
'btn' jhb   'click me'
'res' jhdiv '' 
)

text =: 0 : 0
  unclickable.
)

create =: 3 : 0
  NB. load'/home/michal/r/rsc/cf/webworld.ijs'
  count =: 0
  JS =: JS hrplc 'JPATH';HPATH
  'jgameld28'jhr''
)

jev_get =: create
ev_btn_click =: 3 : 0
  count =: count + 1
  jhrajax ":count
)

JS =: 0 : 0
function ev_btn_click(){jdoajax([],'');}
function ev_btn_click_ajax(ts){jbyid('res').innerHTML=ts;}
function ev_body_load(){
  d3.select('body').style({'background':'red'});
  $('#btn').css({'background':'gold'});
  setInterval(function(){jdoajax([],'',"ev_btn_click''");}, 2500);
}
)


NB. -------------  game stuff --------------------------------------

around =: (1 : '_1 _1 |. [ {.!.x~ >:^:2 @ $ @ ,.')
wsize =: 32 64
world =: 1 around wsize $ 0
spawn =: [: |: 1 1 + wsize ?~ ]

legend =: ' x@%o^'
'blank wall hero enemy gold door' =: i.6
colors =:  (3#256) #: 0 16b999999 16b99ccff 16be23243 16bffcc44 16b66cc99
'N S E W' =: 4 2 $ _1 0   1 0   0 1  0 _1

map =: legend i. noun define
xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
x               x                         x                      x
x               x                         x                      x
x               x                         x   xxxxxxxxxxxxxxx    x
x        @      x                         x                 x    x
x               x                         x                      x
x               x                         x                      x
x               x                         x                      x
x               x                         x                      x
x               x                                xxxxxxxxxxx     x
xxxxxx    xxxxxxx                                x         x     x
x               x                         xxxxxxxx         x     x
x               x                         x                x     x
x                                         x         xxx    x     x
x               x                         x   ^     x      x     x
x               x                         x         x      x     x
xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx  xxxxxxxxxxxxxxxxxxxxxxxx  xxxxxxxx
x           x    x     x                                         x
x   oooo    x    x     x                                         x
x   oooo    x          x                                         x
x   oooo    x          x                                         x
x   oooo    x                                                    x
x   oooo    x    x     x                                         x
x           x    x     x                                         x
xxxxxxxxxxxxxxxxxxxxxxxxxxx xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
x                      x      x             x                    x
x               xxxxxxxx      xxxx    x   xxx     x              x
x               x      x         x    x           x              x
x               x   x  xxxxx  xxxxxxxxxxxxxxxxxxxxxxxxx  xxxxxxxxx
x               x   x     x                        x             x
x                   xxxx  xxxxxxxxxxxxxxxxxxxx     x             x
x                      x                           x      ^      x
x                      x                           x             x
xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
)

world =: (2 2  + wsize) $ map -. 6
hero_at =: 5 5

NB. randomly distribute some gold and monsters
coins   =: spawn 10
enemies =: spawn 25

endworld =: gold (;/coins) } enemy (;/enemies) } world

show =: 3 : 'colors viewmat endworld'

ok =: 2342

