NB. toys for using J on irc

NB. use ascii box drawing so that people can see:
ascii =: 3 : '(9!:7 ''+++++++++|-'') ] y'


NB. whence : finds the script a name was defined in
whence =: verb define
  select. 4!:0 < y
    case. _2 do. 'invalid name'
    case. _1 do. 'name not defined'
    case. 0;1;2;3 do.
      index =. 4!:4 < y
      select. * >: index
        case. 0 do. 'name defined locally'
        case. 1 do. > index { 4!:3''
      end.
  end.
)

NB. botplot : plots a function using unicode
botplot=: [: u: 32 ([:I.9600=]) } 9600 + ([: <. 10* (]-<./) % (>./ - <./))

Note  botplot 2 o. -: i:32

  ▁▃▅▇▉▉▉▇▅▂   ▁▄▆█▉▉█▆▃▁   ▂▅▇▉▊▉▇▅▂   ▁▃▆█▉▉█▆▄▁   ▂▅▇▉▉▉▇▅▃▁

)

NB. 4x4 hex tiles
hext=:u:32,9600+23 22 4 29 16 30 31 24 26 12 25 0 28 27 8
Note c,.1j1#!.(c=.'|')"1] 4 4 $ hext

| |▗|▖|▄|
|▝|▐|▞|▟|
|▘|▚|▌|▙|
|▀|▜|▛|█|

)

NB. lol: removes every other item. (l=1 o=0)
NB. tile uses this to cut out overlapping tiles created by 2 2 <;.3
lol  =: (# $ 1 , 0:) # ]
NB. tile: converts a rank 2 array to an array of of 2x2 boxed tiles
tile =: [: (lol"1)@lol 2 2 <;.3 ]
NB. blit
blit =: (hext{~#.@,L:0)@:tile "2

NB. pb : pretty-prints a boolean matrix in color (uses blit)
pb =: [: ((u:3),'2|',(u:3),'10',((u:3),'2|'),~])"1 blit@(,~^:(1 = {.@$))



NB. --- 1d cellular automata rules ------

seed =: ([,1,]) 31$0
ca   =: 3 :'(0,0,~ 3&(((|._8{.#:y){~#.)\))^:(<10) seed'
rule =: pb@ca
Note rule 250

              ▗▙
             ▗▌▌▙
            ▗▙▗▙▗▙
           ▗▌▙▗▙▗▌▙
          ▗▙  ▗▙  ▗▙
)


NB. -- some tetraminos, for fun. ---
Z =: 1 * 4 4 $ 0 0 0 0, 1 1 0 0,  0 1 1 0,  0 0 0 0
J =: 2 * 4 4 $ 0 0 1 0, 0 0 1 0,  0 1 1 0,  0 0 0 0
T =: 4 * 4 4 $ 0 0 0 0,  0 1 1 1,  0 0 1 0,  0 0 0 0
I =: 4 * 4 4 $ 0 0 1 0
O =: 4 * 4 4 $ 0 0 0 0, 0 1 1 0,  0 1 1 0,  0 0 0 0
S =: +: |. Z
L =: -: |."1 J
shapes=:(O,.S,.L,.T,.J,.Z,.I)

NB. shade and widen:
shade =: [: ((u: 32 9617 9618 9619 9608) {~ ]) (2: # ])"1
Note shade shapes
                  ░░                ▒▒              ██
  ████    ▒▒▒▒    ░░      ██████    ▒▒  ░░░░        ██
  ████  ▒▒▒▒      ░░░░      ██    ▒▒▒▒    ░░░░      ██

)


NB. --- other examples ------------

NB. N×10 bitmaps 0=circles m=mandelbrot set j='YAYJ'
pic0 =: +./ 0.2 0.7 (0.05>|@:-)"0 _ m=:(%>./@,)|j./~ i:4.5
Note blit pic0

 ▞▀▚
▞ ▄ ▚
▌▐ ▌▐
▚ ▀ ▞
 ▚▄▞

)

picm =: -. 2 <| 0&(([ + *:@])^:11~)"0 [ _0.5+|.|:(] j./ [: i: 1j9"_) i:1.5j65
Note   blit picm
                   ▄▄█
        ▖ ▗   ▄▟██████████▄
      ▐▐██████████████████
        ▘ ▝   ▀▜██████████▀
                   ▀▀█

)

mandel =: verb define
  'scale x y w h' =.  6 , 0 _4 , -: 16 16
  2>|((c+*:))^:8 ] c =: scale %~ (x+}.i:w) j./~ (y+}.i:h)
)
Note _ NB. output from `blit mandel''`
   ▐
   ▐
  ▐██
  ▄█▙▖
 ▐████
▗█████▙
 ▝█▛█▛
)


bmp=:'l'&=;._2@,&';'
I=:bmp'oolllloo;oooloooo;oooloooo;oooloooo;oooloooo;oooloooo;oooloooo;oolllooo'
Y=:bmp'oloooloo;oloooloo;oololooo;oolllooo;oooloooo;oooloooo;oooloooo;oooloooo'
A=:bmp'oooloooo;oololooo;oloooloo;oloooloo;ollllloo;oloooloo;oloooloo;oloooloo'
J=:bmp'oolllloo;oooooloo;oooooloo;oooooloo;oooooloo;oooooloo;oloooloo;oolllooo'
picj =: 10{.,.#:Y,.A,.Y,.J
Note blit picj

▌ ▌ ▞▖ ▌ ▌ ▀▜
▐▟ ▐ ▐ ▐▟   ▐
 ▌ ▐▀▜  ▌   ▐
 ▌ ▐ ▐  ▌ ▝▄▞

)

Note blit |:#:i.2^6

        ▄▄▄▄▄▄▄▄▀▀▀▀▀▀▀▀████████
  ▄▄▀▀██  ▄▄▀▀██  ▄▄▀▀██  ▄▄▀▀██
▗▜▗▜▗▜▗▜▗▜▗▜▗▜▗▜▗▜▗▜▗▜▗▜▗▜▗▜▗▜▗▜

)
