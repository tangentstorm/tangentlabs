DECLARE SUB getenter ()
' Michal Wallace
' CASE STATEMENTS -> programs 47-50

QUIT = 0
RANDOMIZE TIMER
WHILE QUIT = 0
 CLS
 COLOR 15
 PRINT "Michal Wallace"
 PRINT "CASE Statements Program"
 PRINT
 PRINT "[A] Program 47  - Random Ages"
 PRINT "[B] Program 48  - Circle Things"
 PRINT "[C] Program 49  - Cable TV Rates"
 PRINT "[D] Program 50  - Graphic Stuff"
 PRINT "[Q] QUIT"
 Menu$ = INPUT$(1)
 SELECT CASE Menu$
  CASE "A", "a"  ' random ages program
   CLS
   COLOR 15
   PRINT "Random ages"
   PRINT "컴컴컴컴컴컴"
   FOR t = 1 TO 5
    age = INT(RND * 30) + 1
    SELECT CASE age
     CASE 1 TO 10
      COLOR 10: PRINT "DRINK A GLASS OF MILK"
     CASE 11 TO 20
      COLOR 14: PRINT "YOU MAY HAVE A DR. PEPPER"
     CASE 21 TO 30
      COLOR 9: PRINT "GO GET WASTED.."
    END SELECT
   NEXT t
   CALL getenter
  CASE "B", "b"
   SCREEN 13
   FOR r = 1 TO 30
    c = INT(RND * 2) + 1
    SELECT CASE c
     CASE 1
      col = INT(RND * 11) + 20
      CIRCLE (100, INT(RND * 101) + 40), 30, col
      PAINT STEP(0, 0), col, col
     CASE 2
      col = INT(RND * 11) + 31
      CIRCLE (250, INT(RND * (115 - 56)) + 56), 50, col
      PAINT STEP(0, 0), col, col
    END SELECT
   NEXT r
   getenter
   SCREEN 0: WIDTH 80
  CASE "C", "c"
   CLS
   COLOR 15
   PRINT "Cable TV Rates"
   PRINT "컴컴컴컴컴컴컴"
   FOR t = 1 TO 10
    COLOR 15
    d = INT(RND * 51)
    PRINT USING "## miles -> "; d;
    SELECT CASE d
     CASE 0 TO 20
      COLOR 12
      PRINT "12 Dollars / Month"
     CASE 21 TO 30
      COLOR 14
      PRINT "23 Dollars / Month"
     CASE 31 TO 50
      COLOR 10
      PRINT "34 Dollars / Month"
    END SELECT
   NEXT t
   getenter
  CASE "D", "d"
   SCREEN 13
   FOR t = 1 TO 80
    X = INT(RND * 4) + 1
    SELECT CASE X
     CASE 1
      l = INT(RND * 31) + 10
      LINE (55, 40)-STEP(l, l), 4, B
     CASE 2
      l = INT(RND * 41) + 30
      LINE (75, 10)-STEP(l, l), 14, B
     CASE 3
      d = INT(RND * 151) + 150
      d2 = INT(RND * 76) + 100
      LINE (200, 100)-(d, d - d2), 9
     CASE 4
      CIRCLE (INT(RND * 76) + 150, INT(RND * 46) + 80), 35, INT(RND * 21) + 60
    END SELECT
   NEXT t
   getenter
   SCREEN 0: WIDTH 80
  CASE "Q", "q"
   QUIT = 1
  CASE ELSE
   BEEP
 END SELECT
WEND

SUB getenter
 COLOR 15
 PRINT
 PRINT "Press Enter"
 DO: LOOP UNTIL INKEY$ = CHR$(13)
END SUB

