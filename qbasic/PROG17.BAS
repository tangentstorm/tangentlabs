'-------------------
' Michal Wallace
'-------------------
' Basic Programs, #17
' Point Slope Thingie
'-------------------
'Psuedocode Junk
'-------------------
'       (Y1 - Y2)
' m = ------------
'       (X1 - X2)
' 1. Get X's and Y's
' 2. Do the Equation
' 3. Output the Results   ( Easy, Huh? )
'-------------------
' Variables
'-------------------
 Index = 0    ' Loop Index
 SlopeX = 0    ' Run
 SlopeY = 0    ' Rise
 X1 = 0       ' X1
 X2 = 0       ' X2
 Y1 = 0       ' Y1
 Y2 = 0       ' Y2
'-------------------
' Data
'-------------------
DATA 7,3,-2,5,14,6,14,17,-8,9,12,9,10,15,8,-11,13,1,-3,4
'-------------------
' The Whole Program Thing
'-------------------
'-----
' Setup the Screen
'-----
SCREEN 0
CLS
COLOR 9: PRINT "ÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ"
COLOR 11: PRINT "Program 17 - the point/slope project"
COLOR 9: PRINT "ÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ"
COLOR 7: PRINT
'-----
' Get Data and perform actions
'-----
  FOR Index = 1 TO 5
    READ X1, Y1, X2, Y2
    IF (X2 - X1) = 0 THEN GOSUB undefined ELSE GOSUB Defined
  NEXT Index
'-------------------
PRINT
COLOR 9: PRINT "ÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ"
COLOR 11: PRINT "Program by Michal Wallace"
COLOR 9: PRINT "ÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ"
COLOR 15
END
'-------------------
'-----
' Subroutines
'-----
undefined:
 COLOR 7
 PRINT "The slope of the line through ("; X1; ","; Y1; ") and ";
 PRINT "("; X2; ","; Y2; ") is";
 COLOR 15
 PRINT " undefined."
RETURN
'-
Defined:
 SlopeY = (Y1 - Y2)
 SlopeX = (X1 - X2)
 IF SlopeX < 0 THEN   ' Fix Negative signs
   SlopeY = -SlopeY
   SlopeX = -SlopeX
 END IF
 COLOR 7
 PRINT "The slope of the line through ("; X1; ","; Y1; ") and ";
 PRINT "("; X2; ","; Y2; ") is ";
 COLOR 15
 PRINT SlopeY; "/"; SlopeX; "."
RETURN

