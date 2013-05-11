'Program Elmo
'By Michal Wallace
'--------------------
REDIM ELMO1(65, 170)
REDIM ELMO2(65, 170)
REDIM ELMO3(65, 170)

SCREEN 12
'------
'ELMO1
'------
x = 50: y = 50
'eyes
CIRCLE (x + 25, y - 5), 5, 9: PAINT (x + 25, y - 5), 15, 9: CIRCLE (x + 25, y - 5), 5
CIRCLE (x + 20, y - 5), 6, 9: PAINT (x + 20, y - 5), 15, 9: CIRCLE (x + 20, y - 5), 5
CIRCLE (x + 23, y - 4), 1, 0
CIRCLE (x + 28, y - 4), 1, 0
'head
CIRCLE (x, y), 25, 7
'mouth
LINE (x, y + 5)-STEP(10, 10), 12: LINE -STEP(9, 0), 12
'hair
DRAW "bm50,25 c10 nh5 nu4 ne5"
'body
DRAW "c7 BM50,75 D50"
DRAW "M-10,+50 NR10 M+10,-50 M+10,+50 NR10" '<-legs
DRAW "bm50,80 m-10,30 nm+5,+15 m+10,-30 m+5,30 m+15,5" '< -arms
GET (20, 10)-(85, 180), ELMO1
'------
'ELMO2
'------
x = 150: y = 50
'eyes
CIRCLE (x + 25, y - 5), 5, 9: PAINT (x + 25, y - 5), 15, 9: CIRCLE (x + 25, y - 5), 5
CIRCLE (x + 20, y - 5), 6, 9: PAINT (x + 20, y - 5), 15, 9: CIRCLE (x + 20, y - 5), 5
CIRCLE (x + 23, y - 4), 1, 0
CIRCLE (x + 28, y - 4), 1, 0
'head
CIRCLE (x, y), 25, 7
'mouth
LINE (x, y + 5)-STEP(10, 10), 12: LINE -STEP(9, 0), 12
'hair
DRAW "bm150,25 c10 nh5 nu4 ne5"
'body
DRAW "c7 BM150,75 D50"
DRAW "M-5,+50 NR10 M+5,-50 M+5,+50 NR10" '<-legs
DRAW "bm150,80 m-20,30 nm+5,+15 m+20,-30 m+20,30 m+10,5" '< -arms
GET (120, 10)-(185, 180), ELMO2
'------
'ELMO3
'------
x = 250: y = 50
'eyes
CIRCLE (x + 25, y - 5), 5, 9: PAINT (x + 25, y - 5), 15, 9: CIRCLE (x + 25, y - 5), 5
CIRCLE (x + 20, y - 5), 6, 9: PAINT (x + 20, y - 5), 15, 9: CIRCLE (x + 20, y - 5), 5
CIRCLE (x + 23, y - 4), 1, 0
CIRCLE (x + 28, y - 4), 1, 0
'head
CIRCLE (x, y), 25, 7
'mouth
LINE (x, y + 5)-STEP(10, 10), 12: LINE -STEP(9, 0), 12
'hair
DRAW "bm250,25 c10 nh5 nu4 ne5"
'body
DRAW "c7 BM250,75 D50"
DRAW "M-10,+50 NR10 M+10,-50 M+10,+50 NR10" '<-legs
DRAW "bm250,80 m-10,30 nm+5,+15 m+10,-30 m+5,30 m+15,5" '< -arms
GET (220, 10)-(285, 180), ELMO3
'----
'MAIN
'----
CLS
z = 0
y = 100
 FOR x = 1 TO 550 STEP 5
  z = z + 1
  SELECT CASE (z MOD 3)
   CASE 0
    PUT (x, y), ELMO1, PSET
   CASE 1
    PUT (x, y), ELMO2, PSET
   CASE 2
    PUT (x, y), ELMO3, PSET
  END SELECT
 IF x > 100 THEN y = y - 5
 IF x > 150 THEN y = y + 10
 IF x > 200 THEN y = y - 5
 NEXT x
 ERASE ELMO1: REDIM ELMO1(1, 1)
 ERASE ELMO2: REDIM ELMO2(1, 1)
 ERASE ELMO3: REDIM ELMO3(1, 1)
END


