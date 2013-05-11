'----------------------
' Michal Wallace
' Tesselation - Clyde
'----------------------

SCREEN 12
DIM Clyde(50, 90)
PALETTE 4, 65536 * 0 + 256 * 0 + 63 'red
PALETTE 3, 65536 * 0 + 256 * 50 + 60 ' brown


'Drawing
DRAW "C6 Bm50,50 r5 f5 d5 l5 g5 d5 h5 u10 e5 bd1 p6,6" 'left ear
DRAW "c6 bm75,50 r5 f5 d10 g5 u5 h5 l5 u5 e5 bd1 p6,6" 'right ear
DRAW "c3 bm60,55 r10 d5 r5 f5 d5 g5 l5 g5 h5 l5 h5 u5 e5 r5 u5 bf1 p3,3" 'head
DRAW "c11bm60,60 r10 f5 g5 u5 l10 d5 h5 e5 bd1 p11,11" 'eyes
DRAW "c6 bm60,65 r10 d5 l10 u5 bf1 p6,6" 'nose
DRAW "c4 bm62,74 f3 e3 l6 br3 bd1 p4,4" 'mouth
DRAW "c15bm60,75 g10 d5 f5 d5 f5 r10 e5 u5 e5 u5 h10 g5 h5 bd1 p15,15" 'chest
DRAW "c3 bm50,80 g10 d50 e10 r5 e5 l5 h10 u10 e5 r5 u5 h5 u5 e5 l5 bd1 p3,3" 'left leg
DRAW "c3 bm75,80 r5 f10 d50 h10 l5 h5 r5 e10 u10 h5 l5 u5 e5 u5 h5 bf10 p3,3" 'right leg

'Outline
DRAW "C0 Bm50,50 r5 f5 d5 l5 g5 d5 h5 u10 e5" 'left ear
DRAW "c0 bm75,50 r5 f5 d10 g5 u5 h5 l5 u5 e5" 'right ear
DRAW "c0 bm60,55 r10 d5 r5 f5 d5 g5 l5 g5 h5 l5 h5 u5 e5 r5 u5" 'head
DRAW "c0 bm60,60 r10 f5 g5 u5 l10 d5 h5 e5 r5 d4 l2 u1 r4 d1 l2" 'eyes
DRAW "c0 bm60,65 r10 d5 l10 u5 bm65,70 d4" 'nose
DRAW "c0 bm62,74 f3 e3 l6" 'mouth
DRAW "c0 bm60,75 g10 d5 f5 d5 f5 r10 e5 u5 e5 u5 h10 g5 h5" 'chest
DRAW "c0 bm50,80 g10 d50 e10 r5 e5 l5 h10 u10 e5 r5 u5 h5 u5 e5 l5" 'left leg
DRAW "c0 bm75,80 r5 f10 d50 h10 l5 h5 r5 e10 u10 h5 l5 u5 e5 u5 h5" 'right leg

'Get Clyde Array
GET (40, 50)-STEP(50, 90), Clyde
CLS

'Tesselating
FOR y = 0 TO 6
 FOR x = 0 TO 11
  PUT (x * 50, y * 50), Clyde, XOR
 NEXT x
NEXT y

LOCATE 26, 23: COLOR 4: PRINT " CLYDE.BAS by Michal Wallace ": COLOR 0

