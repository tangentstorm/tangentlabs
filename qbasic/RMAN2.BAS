'--------------
' ROCKET MAN
'     ][
'--------------
' Game by:
'      Michal
'      Wallace
'--------------
SCREEN 13
DIM Monster1(40, 40)
DIM Monster2(40, 40)
DIM RocketMan(40, 40)
DIM fireball(10, 10)
DIM stars(100, 3)
RANDOMIZE TIMER
'--------------
' Draw Monster1
CLS
 CIRCLE (50, 50), 15, 5: PAINT STEP(0, 0), 13, 5
 CIRCLE (44, 48), 6, 5: CIRCLE (44, 48), 5, 7: PAINT STEP(0, 0), 15, 7
 CIRCLE (56, 48), 6, 5: CIRCLE (56, 48), 5, 7: PAINT STEP(0, 0), 15, 7
 CIRCLE (53, 48), 2, 0: PAINT STEP(0, 0), 0, 0
 CIRCLE (48, 48), 2, 0: PAINT STEP(0, 0), 0, 0
 LINE (45, 55)-(55, 57), 5, BF: LINE (46, 56)-(54, 56), 0
 GET (30, 30)-(70, 70), Monster1
' Draw Monster2
CLS
 DRAW "bm40,40 c2 d20 r20 u20 l5 d10 l10 u10 l5 bf1 p10,2"
 DRAW "bm46,35 c7 d14 r8 u14 l8 bf1 p15,7 bm50,35 c7 d14"
 DRAW "bm47,49 c0 r2 br2 r2 u1 l2 bl2 l2"
 LINE (45, 60)-(55, 62), 2, BF: LINE (46, 61)-(54, 61), 0
 GET (30, 30)-(70, 70), Monster2
' Draw Rocket Man
CLS
 DRAW "bm50,45 c4 f10 l20 e10 bd1 p12,4"
 DRAW "bm45,56 c7 r10 d10 l10 u10 bf1 p15,7"
 DRAW "bm44,60 c4 g5 d5 e5 u5 bdbg p12,4"
 DRAW "bm56,60 c4 f5 d5 h5 u5 bdbf p12,4"
 LINE (49, 60)-(51, 70), 4, BF
 LINE (50, 61)-(50, 69), 12
 GET (30, 30)-(70, 70), RocketMan
CLS
'Draw Fireball
 DRAW "BM42,41 c4 R6 f1 D8 H2 L4 g2 U8 bf1 p4,4"
 DRAW "bm43,42 c12 r4 f1 d5 h1 l4 g1 u5 bf1 p14,12"
 GET (40, 40)-(50, 50), fireball
CLS
'----------------------------------------------------------------
FOR s = 1 TO 100
 stars(s, 1) = INT(RND * 8) + 8
 stars(s, 2) = INT(RND * 320)
 stars(s, 3) = INT(RND * 200)
 PSET (stars(s, 2), stars(s, 3)), stars(s, 1)
NEXT s
WHILE QuitProgram = false
' Draw Title Screen
 LOCATE 7, 12
 COLOR 1: PRINT "="; : COLOR 9: PRINT "="; : COLOR 11: PRINT "=";
 COLOR 15: PRINT "ROCKETMAN";
 COLOR 11: PRINT "="; : COLOR 9: PRINT "="; : COLOR 1: PRINT "="
 LOCATE 5, 16
 COLOR 8: PRINT "Ü"; : COLOR 7: PRINT "Ü"; : COLOR 15: PRINT "Ü Ü";
 COLOR 7: PRINT "Ü"; : COLOR 8: PRINT "Ü"
 LOCATE 6, 18: COLOR 15: PRINT "Û Û"
 LOCATE 8, 18: COLOR 15: PRINT "Û Û"
 LOCATE 9, 16
 COLOR 8: PRINT "ß"; : COLOR 7: PRINT "ß"; : COLOR 15: PRINT "ß ß";
 COLOR 7: PRINT "ß"; : COLOR 8: PRINT "ß"
 LOCATE 15, 13
 PRINT "Press <Enter>"
 LOCATE 24, 30
 COLOR 8: PRINT "Ä"; : COLOR 15: PRINT "S";
 COLOR 7: PRINT "ÅîâL³NG"; : COLOR 8: PRINT "Ä";
 COLOR 0
 WHILE INKEY$ <> CHR$(13): WEND
 CLS
'Set up Screen
true = 1
false = 0
mon2flag = false
frb1flag = false
frb2flag = false
frb3flag = false
QuitProgram = false
m1x = INT(RND * 300): m1y = 0
M2X = INT(RND * 300): M2Y = 0
f1x = 0: f1y = 0
f2x = 0: f2y = 0
f3x = 0: f3y = 0
rmx = 150: rmy = 155
FOR s = 1 TO 100
 PSET (stars(s, 2), stars(s, 3)), stars(s, 1)
NEXT s
PUT (rmx, rmy), RocketMan, XOR
PUT (m1x, m1y), Monster1, XOR
'Main Loop
WHILE QuitGame = false
 IF mon2flag = true THEN PUT (M2X, M2Y), Monster2, XOR
 C$ = INKEY$
 COLOR 4
 IF C$ <> "" THEN
  PUT (rmx, rmy), RocketMan, XOR
  IF C$ = CHR$(0) + "H" THEN
   IF frb1flag = false THEN
    frb1flag = true
    f1x = rmx + 15
    f1y = rmy
    PUT (f1x, f1y), fireball, XOR
   ELSE
    IF frb2flag = false THEN
     frb2flag = true
     f2x = rmx + 15
     f2y = rmy
     PUT (f2x, f2y), fireball, XOR
    ELSE
    IF frb3flag = false THEN
     frb3flag = true
     f3x = rmx + 15
     f3y = rmy
     PUT (f3x, f3y), fireball, XOR
    END IF
   END IF
  END IF
 END IF
  IF C$ = CHR$(27) THEN QuitGame = true
  IF C$ = CHR$(0) + "M" THEN
   rmx = rmx + 5
   IF rmx > 275 THEN rmx = 10
  END IF
  IF C$ = CHR$(0) + "K" THEN
   rmx = rmx - 5
   IF rmx < 10 THEN rmx = 275
  END IF
  PUT (rmx, rmy), RocketMan, XOR
 END IF
 count = count + 1: IF count > 100 THEN count = 0
 IF count = 0 THEN
  PUT (m1x, m1y), Monster1, XOR
  m1y = m1y + 10
  IF m1y > 150 THEN QuitGame = true ELSE PUT (m1x, m1y), Monster1, XOR
 END IF
 IF (count = 10) AND (frb1flag = true) THEN
  PUT (f1x, f1y), fireball, XOR
  f1y = f1y - 10
  IF f1y < 20 THEN frb1flag = false ELSE PUT (f1x, f1y), fireball, XOR
  IF (f1x >= m1x) AND (f1x <= m1x + 40) AND (f1y < m1y + 40) THEN
    GOSUB Zap1
    BEEP
    PUT (f1x, f1y), fireball, XOR
    frb1flag = false
   END IF
 END IF
 IF (count = 20) AND (frb2flag = true) THEN
  PUT (f2x, f2y), fireball, XOR
  f2y = f2y - 10
  IF f2y < 20 THEN frb2flag = false ELSE PUT (f2x, f2y), fireball, XOR
  IF (f2x >= m1x) AND (f2x <= m1x + 40) AND (f2y < m1y + 40) THEN GOSUB Zap1
 END IF
 IF (count = 30) AND (frb3flag = true) THEN
  IF f3y < 20 THEN frb3flag = false ELSE PUT (f3x, f3y), fireball, XOR
  f3y = f3y - 10
  PUT (f3x, f3y), fireball, XOR
  IF (f3x >= m1x) AND (f3x <= m1x + 40) AND (f3y < m1y + 40) THEN GOSUB Zap1
 END IF
WEND
INPUT s
END
WEND


Zap1:
 PUT (m1x, m1y), Monster1, XOR
 m1x = INT(RND * 280): m1y = 0
 PUT (m1x, m1y), Monster1, XOR
RETURN

