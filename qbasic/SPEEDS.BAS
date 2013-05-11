c1 = 1
c2 = 1
x = 1
WHILE INKEY$ = ""
 x = x + 1
 FOR y = 1 TO 10: NEXT y
 IF x MOD 1 = 0 THEN
  SELECT CASE c1
   CASE 1
    OUT 888, 1: c1 = 2
   CASE 2
    OUT 888, 2: c1 = 3
   CASE 3
    OUT 888, 4: c1 = 4
   CASE 4
    OUT 888, 8: c1 = 1
  END SELECT
 END IF
 FOR y = 1 TO 10: NEXT y
 IF x MOD 2 = 0 THEN
  SELECT CASE c2
   CASE 1
    OUT 888, 128: c2 = 2
   CASE 2
    OUT 888, 64: c2 = 3
   CASE 3
    OUT 888, 32: c2 = 4
   CASE 4
    OUT 888, 16: c2 = 1
  END SELECT
 END IF
WEND

