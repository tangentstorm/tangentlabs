'Program SpinPrint
'-------------------
'-----------
' Variables
'-----------
  Message$ = ""   ' Message to print
  Col = 0         ' Colors
  Y = 0           ' Y Value
  X = 0           ' X Value
  LCount = 0      ' String Length Counter
  Xcount = 0      ' Counter for Trip across Screen
  CenX = 41       ' Center
'-----------
' Program
'-----------
CLS
Col = 1
Count = 5
READ Message$
FOR LCount = LEN(Message$) TO 1 STEP -1
 IF Col = 1 THEN COLOR 15
 IF Col = 2 THEN COLOR 11
 IF Col = 3 THEN COLOR 9
 Col = Col + 1: IF Col >= 3 THEN Col = 1
 FOR Xcount = 1 TO (CenX - LEN(Message$) / 2 + LCount - 2)
   X = Xcount * 2 + 1 - Xcount
   LOCATE 1 + Count * 2, X: PRINT " /"
   LOCATE 1 + Count * 2, X: PRINT " Ä"
   LOCATE 1 + Count * 2, X: PRINT " \"
   LOCATE 1 + Count * 2, X: PRINT " ³"
   LOCATE 1 + Count * 2, X: PRINT " "; MID$(Message$, LCount, 1)
 NEXT Xcount
NEXT LCount
COLOR 0
END
'-----------
' Data
'-----------
DATA "ÄÄÄÄÄ=<  S p I n   p R i N t  >=ÄÄÄÄÄ"

