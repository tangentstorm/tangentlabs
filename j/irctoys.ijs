NB. toys for using J on irc

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

lol =: (# $ 1 , 0:) # ]
blit =: ([:(hext{~#.@,L:0)@(lol"1)@lol 2 2 <;.3 ])

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



bmp=:([: #. 'l' = [: (}:"1) 8 9 $ ])
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
