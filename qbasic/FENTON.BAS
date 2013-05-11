'-----------------------
' Michal Wallace
' Tesselation - Fenton
'-----------------------
           
SCREEN 12
PALETTE 4, 65536 * 0 + 256 * 10 + 63  ' Red
PALETTE 14, 65536 * 3 + 256 * 50 + 63 ' Yellow
PALETTE 9, 65536 * 63 + 256 * 10 + 10 ' blue


'Draw Fenton
DRAW "c4 bm120,50 r10 f5 r5 f5 d5 g5 h5 r5 u5 l5 h5 g5 h5 g5 l5 d5 r5 g5 h5 u5 e5 r5 e5 bd1 p4,4" 'Head
DRAW "c15bm120,55 f5 e5 f5 d10 h5 l10 g5 u10 e5 bd1 p15,15" 'Eyes
DRAW "c14bm115,65 d5 e5 r10 f5 u5 f5 d5 g5 l5 g5 h5 l5 h5 u5 e5 d5 bd1 p14,14" 'beak
DRAW "c9 bm110,60 r5 d5 l5 u5 bf1 p9,9 bm 135,60 r5 d5 l5 u5 bf1 p9,9" 'ears
DRAW "c9 bm115,80 r5 f5 e5 r5 g5 f15 g10 d15 g5 d10 l10 u10 h5 u15 h10 e15 h5 bf9 p9,9" 'chest
DRAW "c4 bm50,110 e15 r10 e5 u5 e20 f5 d5 f10 r5 g15 f10 d15 f5 d10 g5 l5 h20 e5 u5 l5 g5 h5 u5 e5 r10 e15 u5 h5 g5 d5 l5 f5 g5 l30 g5 f5 l5 d5 g5 h5 u5 bf1 p4,4" 'left side
DRAW "c14bm70,145 r5 e10 u5 e10 u5 l5 g5 d5 g5 d5 g9 br1 p14,14" 'left leg
DRAW "c4 bm130,85 r5 e10 u5 e5 f20 d5 g5 l10 g15 d5 f5 e5 u5 r5 h5 e5 r30 e5 h5 r5 u5 e5 f5 d5 g15 l10 g5 d5 g5 h5 l5 d5 f5 g20 l5 h5 u10 e5 u15 e10 h15 br10 p4,4" 'right side
DRAW "c14bm155,115 r5 f5 d5 f5 d5 f10 l5 h10 u5 h10  u5 bf1 p14,14" 'right leg

'Outline Fenton
DRAW "c0 bm120,50 r10 f5 r5 f5 d5 g5 h5 r5 u5 l5 h5 g5 h5 g5 l5 d5 r5 g5 h5 u5 e5 r5 e5 bm115,55 r5 f5 e5 r5 bm 125,55 nh3 ne3" 'head
DRAW "c0 bm120,55 f5 e5 f5 d10 h5 l10 g5 u10 e5 bm125,60 d4 l2 u1 r5 d1 l4" 'Eyes
DRAW "c0 bm115,65 d5 e5 r10 f5 u5 f5 d5 g5 l5 g5 h5 l5 h5 u5 e5 d5 bd5 f10 e10 bm122,70 r1 bm128,70 l1" 'beak
DRAW "c0 bm115,80 r5 f5 e5 r5 g5 f15 g10 d15 g5 d10 l10 u10 h5 u15 h10 e15 h5" 'chest
DRAW "c0 bm50,110 e15 r10 e5 u5 e20 f5 d5 f10 r5 g15 f10 d15 f5 d10 g5 l5 h20 e5 u5 l5 g5 h5 u5 e5 r10 e15 u5 h5 g5 d5 l5 f5 g5 l30 g5 f5 l5 d5 g5 h5 u5" 'left side
DRAW "c0 bm70,145 r5 e10 u5 e10 u5 l5 g5 d5 g5 d5 g9" 'left leg
DRAW "c0 bm130,85 r5 e10 u5 e5 f20 d5 g5 l10 g15 d5 f5 e5 u5 r5 h5 e5 r30 e5 h5 r5 u5 e5 f5 d5 g15 l10 g5 d5 g5 h5 l5 d5 f5 g20 l5 h5 u10 e5 u15 e10 h15" 'right side
DRAW "c0 bm155,115 r5 f5 d5 f5 d5 f10 l5 h10 u5 h10  u5" 'right leg

'get Fenton
DIM fenton(150, 95)
GET (50, 50)-(200, 145), fenton
CLS

'Tesselation
FOR x = 0 TO 4
 FOR y = 0 TO 4 STEP 2
  PUT (x * 90, y * 90), fenton, XOR
 NEXT y
NEXT x

