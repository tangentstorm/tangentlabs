'-------------------
' Michal Wallace
'-------------------
' Basic Programs, #16
' Dartboard
'-------------------
' Variables
'-------------------
  Shots = 0  ' Number of Shots
  DartX = 0  ' Dart's X Coordinate
  DartY = 0  ' Dart's Y Coordinate
  Hits = 0   ' Number of Hits
  Score = 0  ' Score.. <Duh>
'-------------------
' Draw DartBoard
'-------------------
SCREEN 0: WIDTH 80, 25
CLS
PRINT : PRINT : PRINT : PRINT : PRINT
COLOR 15
PRINT "         ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿"
PRINT "         ³                   ³"
PRINT "         ³                   ³"
PRINT "         ³                   ³"
PRINT "         ³                   ³"
PRINT "         ³       ÚÄÄÄ¿       ³"
PRINT "         ³       ³   ³       ³"
PRINT "         ³       ³   ³       ³"
PRINT "         ³       ³   ³       ³"
PRINT "         ³       ³   ³       ³"
PRINT "         ³       ³   ³       ³"
PRINT "         ³       ÀÄÄÄÙ       ³"
PRINT "         ³                   ³"
PRINT "         ³                   ³"
PRINT "         ³                   ³"
PRINT "         ³                   ³"
PRINT "         ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ"
COLOR 15, 1: LOCATE 1, 1, 0:
PRINT "                          -=/   Neato Dartboard Thing  \=-                      "
COLOR 15, 5
PRINT "                         -=< (c) 1992 Michal J. Wallace >=-                     "
COLOR 14, 0
LOCATE 5, 55: PRINT "  Number Fired:"
LOCATE 7, 55: PRINT "Number of Hits:"
LOCATE 9, 55: PRINT "         Score:"
'-------------------
' Program
'-------------------
RANDOMIZE TIMER
FOR Shots = 1 TO 10
  DartC = INT(RND * 35) + 5  ' 5 to 40
  DartR = INT(RND * 19) + 5  ' 5 to 24
'----
'Fire!
'----
  COLOR 4, 0: LOCATE 15, 60
  PRINT "-=>     <=-": LOCATE 15, 63: COLOR 12: PRINT "FIRE!"
  DO WHILE INKEY$ <> CHR$(13): LOOP
  LOCATE 15, 60: PRINT "           "
  PLAY "L64O4GFEDCBA"
  COLOR 9, 0: LOCATE DartR, DartC: PRINT "X"
'----
' Update Score
'----
  IF ((DartC <= 30) AND (DartC >= 10) AND (DartR <= 22) AND (DartR >= 6)) THEN
    BEEP
    Score = Score + 4
    Hits = Hits + 1
    IF ((DartC <= 22) AND (DartC >= 18) AND (DartR <= 17) AND (DartR >= 11)) THEN
      PLAY "L64o5bababa"
      Score = Score + 6
    END IF
ELSE
    PLAY "l64o4ab"
    Score = Score - 1
  END IF
'----
'Update Screen
'----
  COLOR 11:
  LOCATE 5, 70: PRINT Shots; "/ 10"     ' Shots
  LOCATE 7, 70: PRINT Hits; "/"; Shots  ' Hits
  IF Score > 0 THEN LOCATE 9, 70 ELSE LOCATE 9, 71
  PRINT Score;            ' Score
NEXT Shots
'-------------------
END
'-------------------

