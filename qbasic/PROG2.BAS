'-------------------
' Michal Wallace
'-------------------
' Basic Programs, #2
' Calculate the OutPut of Three Triangles, One at a Time
'  (base and height will be entered by the user)
'-------------------
' Variables
'-------------------
Tri = 0       ' Loop Index for Number of Triangles
BaseOT = 0    ' Base of Triangle
HeightOT = 0  ' Height Of Triangle
AreaOT = 0    ' Area of the Triangle
'-------------------
' Program
'-------------------
FOR Tri = 1 TO 3
  PRINT
  PRINT "Base of Triangle?"
  INPUT ">", BaseOT
  PRINT
  PRINT "Height of Triangle?"
  INPUT ">", HeightOT
  PRINT
  PRINT "<Computing>"
  PLAY "O3L64abcdefgfedcba"
  AreaOT = HeightOT * BaseOT * .5
  PRINT
  PRINT "Area of Triangle ="; AreaOT; "Square Units."
NEXT Tri
'-------------------
END
'-------------------

