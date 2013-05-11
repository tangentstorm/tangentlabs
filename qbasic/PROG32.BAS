' Michal Wallace
' 1-22-93 p. 5
' Program 32

CLS
LPRINT TAB(30); "GASOLINE COSTS"
LPRINT TAB(25); "------------------------"
LPRINT TAB(17); "MONTH"; TAB(25); "175  200  225  250  275"
LPRINT TAB(17); "--------------------------------"
FOR month = 1 TO 10
 READ month$, gal
 LPRINT TAB(17); month$; TAB(25);
 cost = (gal * 1.25 - 175)
 FOR stars = 1 TO cost \ 5
  LPRINT "*";
 NEXT stars
 LPRINT
NEXT month
END
DATA SEPT, 160, OCT, 164, NOV, 176, DEC, 195, JAN, 204, FEB, 188
DATA MAR, 196, APR, 180, MAY, 160, JUNE, 156

