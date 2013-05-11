SCREEN 12
CLS
'-----------------COLORS
LtBlue = 9: Blue = 1: White = 15: Gray = 7:
'-----------------MAIN BACKGROUND
FOR Count = 1 TO 64 * 2
  LINE (0, Count * 5 + 1)-(640, 0), LtBlue
  LINE (0, Count * 5 + 1)-(640, 320), Blue
NEXT Count

'-----------------LETTER: M---<BACKGROUND>----------
Mx = 25: My = 150
LINE (Mx + 50, My)-(Mx, My), Gray       '-Top of first leg thingie
LINE -(Mx, My + 150), Gray              '-left side of same
LINE -(Mx + 50, My + 150), Gray          '-bottom of same
LINE -(Mx + 50, My + 50), Gray          '-right side of same
LINE -(Mx + 75, My + 75), Gray           '-bottom of left slope
LINE -(Mx + 85, My + 75), Gray            '-blunting slope for shadow
LINE -(Mx + 100, My + 50), Gray          '-bottom of right slope
LINE -(Mx + 100, My + 150), Gray         '-Left side of right leg
LINE -(Mx + 150, My + 150), Gray         '-bottom of same
LINE -(Mx + 150, My), Gray               '-right side of same
LINE -(Mx + 100, My), Gray               '-Top of same
LINE -(Mx + 75, My + 25), Gray           '-top of right slope
LINE -(Mx + 50, My), Gray               '-Top of left Slope
PAINT (Mx + 1, My + 1), Gray
'-----------------LETTER: M---<FOREGROUND>----------
Mx = 35: My = 150
LINE (Mx + 50, My)-(Mx, My), White       '-Top of first leg thingie
LINE -(Mx, My + 150), White              '-left side of same
LINE -(Mx + 50, My + 150), White          '-bottom of same
LINE -(Mx + 50, My + 50), White          '-right side of same
LINE -(Mx + 75, My + 75), White           '-bottom of left slope
LINE -(Mx + 100, My + 50), White           '-bottom of right slope
LINE -(Mx + 100, My + 150), White         '-Left side of right leg
LINE -(Mx + 150, My + 150), White         '-bottom of same
LINE -(Mx + 150, My), White               '-right side of same
LINE -(Mx + 100, My), White               '-Top of same
LINE -(Mx + 75, My + 25), White           '-top of right slope
LINE -(Mx + 50, My), White               '-Top of left Slope
PAINT (Mx + 1, My + 1), White
'-----------------LETTER: J---<BACKGROUND>----------
 Mx = 205: My = 150
LINE (Mx, My + 75)-(Mx, My + 125), Gray    ' Left Side of Left Thingie
LINE -(Mx + 25, My + 150), Gray            ' Left Slope
LINE -(Mx + 100, My + 150), Gray          ' Bottom
LINE -(Mx + 125, My + 125), Gray          ' Right Slope
LINE -(Mx + 125, My), Gray                ' Right Side of Right Thingie
LINE -(Mx + 75, My), Gray                 ' Top of Right Thingie
LINE -(Mx + 75, My + 100), Gray           ' Left Side of Right Thingie
LINE -(Mx + 50, My + 100), Gray           ' Top of Bridge
LINE -(Mx + 50, My + 75), Gray           ' Right Side of Left Thingie
LINE -(Mx, My + 75), Gray                ' Top of Left Thingie
PAINT (Mx + 1, My + 76), Gray
'-----------------LETTER: J---<FOREGROUND>----------
 Mx = 215: My = 150
LINE (Mx, My + 75)-(Mx, My + 125), White    ' Left Side of Left Thingie
LINE -(Mx + 25, My + 150), White            ' Left Slope
LINE -(Mx + 100, My + 150), White          ' Bottom
LINE -(Mx + 125, My + 125), White          ' Right Slope
LINE -(Mx + 125, My), White               ' Right Side of Right Thingie
LINE -(Mx + 75, My), White                 ' Top of Right Thingie
LINE -(Mx + 75, My + 100), White           ' Left Side of Right Thingie
LINE -(Mx + 50, My + 100), White           ' Top of Bridge
LINE -(Mx + 50, My + 75), White           ' Right Side of Left Thingie
LINE -(Mx, My + 75), White                ' Top of Left Thingie
PAINT (Mx + 1, My + 76), White
'-----------------LETTER: W---<BACKGROUND>----------
Mx = 360: My = 150
LINE (Mx + 50, My)-(Mx, My), Gray       '-Top of first leg thingie
LINE -(Mx, My + 150), Gray              '-left side of same
LINE -(Mx + 50, My + 150), Gray          '-bottom of same
LINE -(Mx + 75, My + 125), Gray         ' Left, Bottom Slope
LINE -(Mx + 100, My + 150), Gray        ' Right, Bottom Slope
LINE -(Mx + 150, My + 150), Gray        ' Bottom of right leg
LINE -(Mx + 150, My), Gray              ' Right Side of right leg
LINE -(Mx + 100, My), Gray              ' Top of Same
LINE -(Mx + 100, My + 100), Gray        ' Left Side of Same
LINE -(Mx + 85, My + 75), Gray          ' Right Top Slope
LINE -(Mx + 75, My + 75), Gray          ' Blunting Slope for Bacground
LINE -(Mx + 50, My + 100), Gray         ' Right Side of Left Leg
LINE -(Mx + 50, My), Gray               ' Top of Left Leg
PAINT (Mx + 1, My + 1), Gray
'-----------------LETTER: W---<FOREGROUND>----------
Mx = 370: My = 150
LINE (Mx + 50, My)-(Mx, My), White       '-Top of first leg thingie
LINE -(Mx, My + 150), White              '-left side of same
LINE -(Mx + 50, My + 150), White          '-bottom of same
LINE -(Mx + 75, My + 125), White         ' Left, Bottom Slope
LINE -(Mx + 100, My + 150), White        ' Right, Bottom Slope
LINE -(Mx + 150, My + 150), White        ' Bottom of right leg
LINE -(Mx + 150, My), White              ' Right Side of right leg
LINE -(Mx + 100, My), White              ' Top of Same
LINE -(Mx + 100, My + 100), White        ' Left Side of Same
LINE -(Mx + 75, My + 75), White          ' Right Top Slope
LINE -(Mx + 50, My + 100), White         ' Right Side of Left Leg
LINE -(Mx + 50, My), White               ' Top of Left Leg
PAINT (Mx + 1, My + 1), White

