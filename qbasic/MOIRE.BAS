'Program Moire  (c) 1992 MJW
'-------------------------------
SCREEN 12
Col1 = 15: Col2 = 0
False = 0: True = 1: NotOver = True
RANDOMIZE TIMER
'-------------------------------
WHILE NotOver = True
'------------------------------
CenX = INT(RND * 640): CenY = INT(RND * 480)
'Col1 = INT(RND * 16):
Col2 = INT(RND * 15)
CLS
'-------------------------------
FOR XCount = 0 TO 640 STEP 2
  LINE (XCount, 0)-(CenX, CenY), Col1
  LINE (XCount + 1, 0)-(CenX, CenY), Col2
  LINE (XCount, 480)-(CenX, CenY), Col1
  LINE (XCount + 1, 480)-(CenX, CenY), Col2
NEXT XCount
'-------------------------------
FOR YCount = 0 TO 480 STEP 2
  LINE (0, YCount)-(CenX, CenY), Col1
  LINE (0, YCount + 1)-(CenX, CenY), Col2
  LINE (640, YCount)-(CenX, CenY), Col1
  LINE (640, YCount + 1)-(CenX, CenY), Col2
NEXT YCount
'-------------------------------
IF INKEY$ <> "" THEN NotOver = False
WEND
SCREEN 0, 0, 0

